/** @file
  OpenCore driver.

Copyright (c) 2019, vit9696. All rights reserved.<BR>
This program and the accompanying materials
are licensed and made available under the terms and conditions of the BSD License
which accompanies this distribution.  The full text of the license may be found at
http://opensource.org/licenses/bsd-license.php

THE PROGRAM IS DISTRIBUTED UNDER THE BSD LICENSE ON AN "AS IS" BASIS,
WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.

**/

#include <Base.h>

#include <Library/OcMainLib.h>

#include <Library/BaseLib.h>
#include <Library/DebugLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/OcAfterBootCompatLib.h>
#include <Library/OcAppleKernelLib.h>
#include <Library/OcMiscLib.h>
#include <Library/OcAppleImg4Lib.h>
#include <Library/OcStringLib.h>
#include <Library/OcVirtualFsLib.h>
#include <Library/PrintLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiRuntimeServicesTableLib.h>
#include <Protocol/SimpleFileSystem.h>

typedef enum {
  DUMP_TYPE_PREPATCHED,
  DUMP_TYPE_PREPROCESSED,
  DUMP_TYPE_PATCHED
} DUMP_TYPE;

typedef enum {
  KERNEL_TYPE_PLAIN,
  KERNEL_TYPE_PRELINKED,
  KERNEL_TYPE_MKEXT
} KERNEL_TYPE;

STATIC OC_STORAGE_CONTEXT  *mOcStorage;
STATIC OC_GLOBAL_CONFIG    *mOcConfiguration;
STATIC OC_CPU_INFO         *mOcCpuInfo;
STATIC UINT8               mKernelDigest[SHA384_DIGEST_SIZE];

STATIC UINT32   mOcDarwinVersion;
STATIC BOOLEAN  mUse32BitKernel;

STATIC CACHELESS_CONTEXT  mOcCachelessContext;
STATIC BOOLEAN            mOcCachelessInProgress;

STATIC EFI_FILE_PROTOCOL  *mCustomKernelDirectory;
STATIC BOOLEAN            mCustomKernelDirectoryInProgress;

//
// Helper to find all occurrences of Substring in String.
//
STATIC
CONST VOID *
OcAsciiSearch (
  IN CONST VOID  *String,
  IN UINTN       StringSize,
  IN CONST VOID  *Substring,
  IN UINTN       SubstringSize
  )
{
  CONST UINT8  *Str;
  CONST UINT8  *Sub;
  UINTN        Index;

  if ((SubstringSize == 0) || (StringSize < SubstringSize)) {
    return NULL;
  }

  Str = String;
  Sub = Substring;

  for (Index = 0; Index <= StringSize - SubstringSize; Index++) {
    if (CompareMem (&Str[Index], Sub, SubstringSize) == 0) {
      return &Str[Index];
    }
  }

  return NULL;
}

//
// Helper to convert a hexadecimal character string to a byte array.
//
STATIC
EFI_STATUS
OcHexStringToBytes (
  IN  CONST CHAR8  *HexString,
  OUT UINT8        **Bytes,
  OUT UINTN        *BytesSize
  )
{
  UINTN       HexStringLen;
  UINTN       Index;
  UINT8       Digit;
  UINT8       ByteValue;

  HexStringLen = AsciiStrLen (HexString);
  if ((HexStringLen % 2) != 0) {
    return EFI_INVALID_PARAMETER;
  }

  *BytesSize = HexStringLen / 2;
  *Bytes     = AllocatePool (*BytesSize);
  if (*Bytes == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  for (Index = 0; Index < *BytesSize; ++Index) {
    // High nibble
    Digit = HexString[Index * 2];
    if (Digit >= '0' && Digit <= '9') {
      ByteValue = (Digit - '0') << 4;
    } else if (Digit >= 'a' && Digit <= 'f') {
      ByteValue = (Digit - 'a' + 10) << 4;
    } else if (Digit >= 'A' && Digit <= 'F') {
      ByteValue = (Digit - 'A' + 10) << 4;
    } else {
      FreePool (*Bytes);
      return EFI_INVALID_PARAMETER;
    }

    // Low nibble
    Digit = HexString[Index * 2 + 1];
    if (Digit >= '0' && Digit <= '9') {
      ByteValue |= (Digit - '0');
    } else if (Digit >= 'a' && Digit <= 'f') {
      ByteValue |= (Digit - 'a' + 10);
    } else if (Digit >= 'A' && Digit <= 'F') {
      ByteValue |= (Digit - 'A' + 10);
    } else {
      FreePool (*Bytes);
      return EFI_INVALID_PARAMETER;
    }

    (*Bytes)[Index] = ByteValue;
  }

  return EFI_SUCCESS;
}

STATIC
UINTN
OcKernelScanForHexSignature (
  IN CONST UINT8  *Buffer,
  IN UINT32       BufferSize,
  IN CONST CHAR8  *HexSignature,
  IN CONST CHAR8  *Comment
  )
{
  UINTN        Finds;
  CONST UINT8  *LastFound;
  UINTN        SearchOffset;
  UINT8        *SignatureBytes;
  UINTN        SignatureSize;
  EFI_STATUS   Status;

  if (HexSignature == NULL) {
    return 0;
  }

  Finds  = 0;
  Status = OcHexStringToBytes (HexSignature, &SignatureBytes, &SignatureSize);
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Invalid hex string for signature %a\n", Comment));
    return 0;
  }

  SearchOffset = 0;
  while (SearchOffset < BufferSize) {
    LastFound = OcAsciiSearch (Buffer + SearchOffset, BufferSize - SearchOffset, SignatureBytes, SignatureSize);
    if (LastFound != NULL) {
      DEBUG ((
        DEBUG_INFO,
        "OC: Found %a at kernel offset 0x%08X\n",
        Comment,
        (UINT32)(LastFound - Buffer)
        ));
      SearchOffset = (LastFound - Buffer) + SignatureSize;
      Finds++;
    } else {
      break;
    }
  }

  FreePool (SignatureBytes);

  return Finds;
}

STATIC
VOID
OcTestKernelPatch (
  IN CONST UINT8  *Kernel,
  IN UINT32       KernelSize,
  IN CONST CHAR8  *OriginalHex,
  IN CONST CHAR8  *PatchedHex,
  IN CONST CHAR8  *Comment,
  IN CONST CHAR8  *HexOffset     OPTIONAL
  )
{
  UINTN        OriginalFinds;
  UINTN        PatchedFinds;
  UINT8        *OriginalBytes;
  UINTN        OriginalSize;
  UINT8        *PatchedBytes;
  UINTN        PatchedSize;
  EFI_STATUS   Status;
  UINTN        TargetOffset;
  CHAR8        FormattedComment[128];

  // If no original signature is provided, there is nothing to test.
  if (OriginalHex == NULL) {
    DEBUG ((DEBUG_INFO, "OC: No signature provided for %a, skipping check\n", Comment));
    return;
  }

  // If a specific offset is provided, check only there.
  if (HexOffset != NULL) {
    Status = AsciiStrHexToUintnS (HexOffset, NULL, &TargetOffset);
    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_WARN, "OC: Invalid HexOffset %a for patch %a\n", HexOffset, Comment));
      return;
    }

    // Get original bytes
    Status = OcHexStringToBytes (OriginalHex, &OriginalBytes, &OriginalSize);
    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_WARN, "OC: Invalid OriginalHex for patch %a\n", Comment));
      return;
    }

    // Check bounds
    if (TargetOffset + OriginalSize > KernelSize) {
      DEBUG ((DEBUG_INFO, "OC: Signature for %a not found at specified offset 0x%08X (out of bounds)\n", Comment, (UINT32)TargetOffset));
      FreePool (OriginalBytes);
      return;
    }

    // Check for original signature
    if (CompareMem (Kernel + TargetOffset, OriginalBytes, OriginalSize) == 0) {
      DEBUG ((DEBUG_INFO, "OC: Found %a (Original) at specified offset 0x%08X\n", Comment, (UINT32)TargetOffset));
      FreePool (OriginalBytes);
      return;
    }

    // At this point, we know it's not the original signature.
    // Case 1: Check for ANY modification (PatchedHex is NULL)
    if (PatchedHex == NULL) {
      DEBUG ((DEBUG_INFO, "OC: Found %a (Modified) at specified offset 0x%08X\n", Comment, (UINT32)TargetOffset));
      FreePool (OriginalBytes);
      return;
    }

    // Case 2: Check for a SPECIFIC patch (PatchedHex is not NULL)
    Status = OcHexStringToBytes (PatchedHex, &PatchedBytes, &PatchedSize);
    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_WARN, "OC: Invalid PatchedHex for patch %a\n", Comment));
      FreePool (OriginalBytes);
      return;
    }

    if ((TargetOffset + PatchedSize <= KernelSize) && (CompareMem (Kernel + TargetOffset, PatchedBytes, PatchedSize) == 0)) {
      DEBUG ((DEBUG_INFO, "OC: Found %a (Patched) at specified offset 0x%08X\n", Comment, (UINT32)TargetOffset));
    } else {
      DEBUG ((DEBUG_INFO, "OC: Signature for %a not found at specified offset 0x%08X\n", Comment, (UINT32)TargetOffset));
    }

    FreePool (PatchedBytes);
    FreePool (OriginalBytes);
    return;
  } else {
    // Global search logic
    AsciiSPrint (FormattedComment, sizeof (FormattedComment), "%a (Original)", Comment);
    OriginalFinds = OcKernelScanForHexSignature (Kernel, KernelSize, OriginalHex, FormattedComment);

    if (PatchedHex != NULL) {
      AsciiSPrint (FormattedComment, sizeof (FormattedComment), "%a (Patched)", Comment);
      PatchedFinds = OcKernelScanForHexSignature (Kernel, KernelSize, PatchedHex, FormattedComment);
    } else {
      PatchedFinds = 0;
    }

    if (OriginalFinds == 0 && PatchedFinds == 0) {
      DEBUG ((DEBUG_INFO, "OC: Signature for %a not found anywhere\n", Comment));
    }
  }
}

STATIC
VOID
OcTestAMDSignatures (
  IN CONST UINT8  *Kernel,
  IN UINT32       KernelSize
  )
{
  // Get the major Darwin version (e.g., 17 for 10.13.x, 16 for 10.12.x, and so on)
  UINT32 MajorDarwinVersion = mOcDarwinVersion / 10000;

  DEBUG ((DEBUG_INFO, "OC: Running common Kernel Patch signature tests...\n"));

  // Check if the current OS is High Sierra (Darwin 17)
  if (MajorDarwinVersion == 17) {
    OcTestKernelPatch (Kernel, KernelSize, "00252E2A7300",
                                           "00002E2A7300", "PanicKextDump", "0x007ED68C");
    OcTestKernelPatch (Kernel, KernelSize, "B901000100",
                                           NULL, "ProvideCurrentCpuInfoZeroMsrThreadCoreCount", "0x00174640");
    OcTestKernelPatch (Kernel, KernelSize, "C1E81AFFC089",
                                           NULL, "Force cpuid_cores_per_package | user defined CPU cores", "0x00174CA5");
    OcTestKernelPatch (Kernel, KernelSize, "B9A00100000F32",
                                           "66906690669090", "_commpage_populate | Remove rdmsr", "0x0018AA3F");
    OcTestKernelPatch (Kernel, KernelSize, "B8040000004489F14489",
                                           "B81D0000804489F14489", "_cpuid_set_cache_info | Update Intel Leaf to AMD Leaf", "0x00174C63");
    OcTestKernelPatch (Kernel, KernelSize, "B98B00000031C031D20F30",
                                           "6690669066906690669090", "_cpuid_set_generic_info | Remove wrmsr(0x8B)", "0x001737D0");
    OcTestKernelPatch (Kernel, KernelSize, "B98B0000000F32",
                                           "BABA0000006690", "_cpuid_set_generic_info | Replace rdmsr(0x8B)", "0x0017381B");
    OcTestKernelPatch (Kernel, KernelSize, "B9170000000F32C1EA1280E207",
                                           "B201660F1F8400000000006690", "_cpuid_set_generic_info | Set flag=1", "0x00173897");
    OcTestKernelPatch (Kernel, KernelSize, "003A0F82",
                                           "00000F82", "_cpuid_set_generic_info | Disable Check for Leaf 7", "0x001742DF");
    OcTestKernelPatch (Kernel, KernelSize, "47656E75696E65496E74656C00",
                                           "41757468656E746963414D4400", "Strings Replace | GenuineIntel/AuthenticAMD Vendor", "0x0076E431");
    OcTestKernelPatch (Kernel, KernelSize, "31DB803DB80B8D0006755C",
                                           "BBBC4FEA78E95D00000090", "_cpuid_set_cpufamily | Force CPUFAMILY_INTEL_PENRYN", "0x0017448B");
    OcTestKernelPatch (Kernel, KernelSize, "B9990100000F3248C1E22089C64809D6B9980100000F3248C1E22089C04809C2BF5802310531C94531C0",
                                           "660F1F840000000000660F1F840000000000660F1F840000000000660F1F840000000000660F1F440000", "_i386_init/_pstate_trace | Remove rdmsr calls", NULL);
    OcTestKernelPatch (Kernel, KernelSize, "25FC00000083F813",
                                           "25FC0000000F1F00", "_lapic_init | Remove version check", "0x0018DC1D");
    OcTestKernelPatch (Kernel, KernelSize, "89C081E2FFFFF0FF81CA00000100B977020000",
                                           "B977020000B806010700BA060107000F1F4000", "_mtrr_update_action | Set PAT MSR to 00070106h", "0x00194459");
  
  // Check if the current OS is Sierra (Darwin 16)
  } else if (MajorDarwinVersion == 16) {
    OcTestKernelPatch (Kernel, KernelSize, "00252E2A7300",
                                           "00002E2A7300", "PanicKextDump", "0x007EEEB0");
    OcTestKernelPatch (Kernel, KernelSize, "B901000100",
                                           NULL, "ProvideCurrentCpuInfoZeroMsrThreadCoreCount", "0x003F64F6");
    OcTestKernelPatch (Kernel, KernelSize, "C1EA1AFFC289",
                                           NULL, "Force cpuid_cores_per_package | user defined CPU cores", "0x001ED1FE");
    OcTestKernelPatch (Kernel, KernelSize, "B9A00100000F32",
                                           "66906690669090", "_commpage_populate | Remove rdmsr", "0x0020194B");
    OcTestKernelPatch (Kernel, KernelSize, "B8040000004489F94489",
                                           "B81D0000804489F94489", "_cpuid_set_cache_info | Update Intel Leaf to AMD Leaf", "0x001ED1B3");
    OcTestKernelPatch (Kernel, KernelSize, "B98B00000031C031D20F30",
                                           "6690669066906690669090", "_cpuid_set_generic_info | Remove wrmsr(0x8B)", "0x001EC21E");
    OcTestKernelPatch (Kernel, KernelSize, "B98B0000000F32",
                                           "BABA0000006690", "_cpuid_set_generic_info | Replace rdmsr(0x8B)", "0x001EC269");
    OcTestKernelPatch (Kernel, KernelSize, "B9170000000F32C1EA1280E207",
                                           "B201660F1F8400000000006690", "_cpuid_set_generic_info | Set flag=1", "0x001EC2E4");
    OcTestKernelPatch (Kernel, KernelSize, "0FB60552A3700083F83A0F82B1000000",
                                           "0FB60552A3700083F8000F82B1000000", "_cpuid_set_generic_info | Disable Check for Leaf 7", "0x001ECD2C");
    OcTestKernelPatch (Kernel, KernelSize, "47656E75696E65496E74656C00",
                                           "41757468656E746963414D4400", "Strings Replace | GenuineIntel/AuthenticAMD Vendor", "0x0077E06B");
    OcTestKernelPatch (Kernel, KernelSize, "31DB0FB6C883F906755A",
                                           "BBBC4FEA78E95A000000", "_cpuid_set_cpufamily | Force CPUFAMILY_INTEL_PENRYN", "0x001ECEE2");
    OcTestKernelPatch (Kernel, KernelSize, "B9990100000F3248C1E22089C64809D6B9980100000F3248C1E22089C04809C2BF5802310531C94531C0",
                                           "660F1F840000000000660F1F840000000000660F1F840000000000660F1F840000000000660F1F440000", "_i386_init/_pstate_trace | Remove rdmsr calls", NULL);
    OcTestKernelPatch (Kernel, KernelSize, "25FC00000083F813",
                                           "25FC0000000F1F00", "_lapic_init | Remove version check", "0x00204CBD");
    OcTestKernelPatch (Kernel, KernelSize, "89C081E2FFFFF0FF4881CA00000100B977020000",
                                           "B806010700BA06010700660F1F84000000000090", "_mtrr_update_action | Set PAT MSR to 00070106h", "0x0020BA99");
  } else if (MajorDarwinVersion == 15) {
    OcTestKernelPatch (Kernel, KernelSize, "00252E2A7300",
                                           NULL, "PanicKextDump", "0x007F15EE");
    OcTestKernelPatch (Kernel, KernelSize, "B901000100",
                                           NULL, "ProvideCurrentCpuInfoZeroMsrThreadCoreCount", "0x003CA970");
    OcTestKernelPatch (Kernel, KernelSize, "C1EA1AFFC289",
                                           NULL, "Force cpuid_cores_per_package | user defined CPU cores", "0x001BC58E");
    OcTestKernelPatch (Kernel, KernelSize, "B9A00100000F32",
                                           "66906690669090", "_commpage_populate | Remove rdmsr", "0x001D1B56");
    OcTestKernelPatch (Kernel, KernelSize, "B8040000004489F94489",
                                           "B81D0000804489F94489", "_cpuid_set_cache_info | Update Intel Leaf to AMD Leaf", "0x001BC543");
    OcTestKernelPatch (Kernel, KernelSize, "B98B00000031C031D20F30",
                                           "6690669066906690669090", "_cpuid_set_generic_info | Remove wrmsr(0x8B)", "0x001BB51E");
    OcTestKernelPatch (Kernel, KernelSize, "B98B0000000F32",
                                           "BABA0000006690", "_cpuid_set_generic_info | Replace rdmsr(0x8B)", "0x001BB569");
    OcTestKernelPatch (Kernel, KernelSize, "B9170000000F32C1EA1280E207",
                                           "B201660F1F8400000000006690", "_cpuid_set_generic_info | Set flag=1", "0x001BB5E4");
    OcTestKernelPatch (Kernel, KernelSize, "0FB60519A0700083F83A0F82B1000000",
                                           "0FB60519A0700083F8000F82B1000000", "_cpuid_set_generic_info | Disable Check for Leaf 7", "0x001BC02D");
    OcTestKernelPatch (Kernel, KernelSize, "47656E75696E65496E74656C00",
                                           "41757468656E746963414D4400", "Strings Replace | GenuineIntel/AuthenticAMD Vendor", "0x007726A9");
    OcTestKernelPatch (Kernel, KernelSize, "31DB0FB6C883F9060F85D1000000",
                                           "BBBC4FEA78E9D50000000F1F4000", "_cpuid_set_cpufamily | Force CPUFAMILY_INTEL_PENRYN", "0x001BC1F2");
    OcTestKernelPatch (Kernel, KernelSize, "B9990100000F3248C1E22089C64809D6B9980100000F3248C1E22089C04809C2BF5802310531C94531C0",
                                           "660F1F840000000000660F1F840000000000660F1F840000000000660F1F840000000000660F1F440000", "_i386_init/_pstate_trace | Remove rdmsr calls", NULL);
    OcTestKernelPatch (Kernel, KernelSize, "25FC00000083F813",
                                           "25FC0000000F1F00", "_lapic_init | Remove version check", "0x001D4FEB");
    OcTestKernelPatch (Kernel, KernelSize, "89C081E2FFFFF0FF4881CA00000100B977020000",
                                           "B806010700BA06010700660F1F84000000000090", "_mtrr_update_action | Set PAT MSR to 00070106h", "0x001DC3D8");
  } else if (MajorDarwinVersion == 14) {
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "PanicKextDump", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "ProvideCurrentCpuInfoZeroMsrThreadCoreCount", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "Force cpuid_cores_per_package | user defined CPU cores", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_commpage_populate | Remove rdmsr", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_cpuid_set_cache_info | Update Intel Leaf to AMD Leaf", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_cpuid_set_generic_info | Remove wrmsr(0x8B)", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_cpuid_set_generic_info | Replace rdmsr(0x8B)", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_cpuid_set_generic_info | Set flag=1", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_cpuid_set_generic_info | Disable Check for Leaf 7", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "Strings Replace | GenuineIntel/AuthenticAMD Vendor", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_cpuid_set_cpufamily | Force CPUFAMILY_INTEL_PENRYN", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_i386_init/_pstate_trace | Remove rdmsr calls", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_lapic_init | Remove version check", NULL);
    OcTestKernelPatch (Kernel, KernelSize, NULL,
                                           NULL, "_mtrr_update_action | Set PAT MSR to 00070106h", NULL);
  } else {
  // For any other detected unsupported version
    DEBUG ((
      DEBUG_INFO,
      "OC: Skipping common patch signature tests for unsupported/unknown Darwin version %u.\n",
      mOcDarwinVersion
      ));
  }
}

STATIC
VOID
OcKernelDumpBuffer (
  IN VOID         *Buffer,
  IN UINT32       BufferSize,
  IN DUMP_TYPE    DumpType,
  IN KERNEL_TYPE  KernelType,
  IN UINT32       DarwinVersion
  )
{
  EFI_STATUS         Status;
  EFI_FILE_PROTOCOL  *Root;
  EFI_FILE_PROTOCOL  *FileHandle;
  CHAR16             FileName[128];
  UINTN              WriteSize;
  EFI_TIME           BootTime;
  UINT32             MajorXnu;
  UINT32             MinorXnu;
  UINT32             PatchXnu;
  CONST CHAR16       *Prefix;

  Status = gRT->GetTime (&BootTime, NULL);
  if (EFI_ERROR (Status)) {
    ZeroMem (&BootTime, sizeof (BootTime));
    BootTime.Year = 2077;
  }

  MajorXnu = DarwinVersion / 10000;
  MinorXnu = (DarwinVersion / 100) % 100;
  PatchXnu = DarwinVersion % 100;

  Prefix = NULL;

  if (DumpType == DUMP_TYPE_PREPATCHED) {
    if (KernelType == KERNEL_TYPE_PRELINKED) {
      Prefix = L"PrePatchedPrelinkedKernel";
    } else if (KernelType == KERNEL_TYPE_MKEXT) {
      Prefix = L"PrePatchedMkext";
    } else {
      Prefix = L"PrePatchedKernel";
    }
  } else if (DumpType == DUMP_TYPE_PREPROCESSED) {
    if (KernelType == KERNEL_TYPE_PRELINKED) {
      Prefix = L"PreProcessedPrelinkedKernel";
    }
    // Add other kernel types if needed for pre-processing dump
  } else { // DUMP_TYPE_PATCHED
    if (KernelType == KERNEL_TYPE_PRELINKED) {
      Prefix = L"PatchedPrelinkedKernel";
    } else if (KernelType == KERNEL_TYPE_MKEXT) {
      Prefix = L"PatchedMkext";
    } else {
      Prefix = L"PatchedKernel";
    }
  }
  
  if (Prefix == NULL) {
    DEBUG ((DEBUG_WARN, "OC: Unknown dump type %d for kernel type %d\n", DumpType, KernelType));
    return;
  }

  //
  // Construct the filename. e.g., PatchedPrelinkedKernel-2025-06-25-111300-16-7-0
  //
  UnicodeSPrint (
    FileName,
    sizeof (FileName),
    L"%s-%04u-%02u-%02u-%02u%02u%02u-%u.%u.%u",
    Prefix,
    BootTime.Year,
    BootTime.Month,
    BootTime.Day,
    BootTime.Hour,
    BootTime.Minute,
    BootTime.Second,
    MajorXnu,
    MinorXnu,
    PatchXnu
    );

  DEBUG ((DEBUG_INFO, "OC: Dumping buffer to %s (%u bytes)...\n", FileName, BufferSize));

  Status = OcFindWritableOcFileSystem (&Root);
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Could not find writable filesystem to dump - %r\n", Status));
    return;
  }

  Status = Root->Open (Root, &FileHandle, FileName, EFI_FILE_MODE_READ | EFI_FILE_MODE_WRITE, 0);
  if (!EFI_ERROR (Status)) {
    FileHandle->Delete (FileHandle);
  }

  Status = Root->Open (
                   Root,
                   &FileHandle,
                   FileName,
                   EFI_FILE_MODE_CREATE | EFI_FILE_MODE_WRITE | EFI_FILE_MODE_READ,
                   0
                   );

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Failed to create %s - %r\n", FileName, Status));
    Root->Close (Root);
    return;
  }

  WriteSize = BufferSize;
  Status    = FileHandle->Write (FileHandle, &WriteSize, Buffer);

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Failed to write to %s - %r\n", FileName, Status));
  } else {
    DEBUG ((DEBUG_INFO, "OC: Successfully dumped %u bytes to %s\n", (UINT32)WriteSize, FileName));
  }

  FileHandle->Close (FileHandle);
  Root->Close (Root);
}

STATIC
VOID
OcDumpVirtualizedKernel (
  IN VOID       *Buffer,
  IN UINT32     BufferSize
  )
{
  EFI_STATUS         Status;
  EFI_FILE_PROTOCOL  *Root;
  EFI_FILE_PROTOCOL  *FileHandle;
  CHAR16             FileName[128];
  UINTN              WriteSize;
  EFI_TIME           BootTime;

  //
  // Construct a unique filename to avoid overwrites.
  //
  Status = gRT->GetTime (&BootTime, NULL);
  if (EFI_ERROR (Status)) {
    ZeroMem (&BootTime, sizeof (BootTime));
    BootTime.Year = 2077;
  }

  UnicodeSPrint (
    FileName,
    sizeof (FileName),
    L"VirtualizedKernel-%04u-%02u-%02u-%02u%02u%02u",
    BootTime.Year,
    BootTime.Month,
    BootTime.Day,
    BootTime.Hour,
    BootTime.Minute,
    BootTime.Second
    );

  DEBUG ((DEBUG_INFO, "OC: Dumping virtualized kernel to %s (%u bytes)...\n", FileName, BufferSize));
  Status = OcFindWritableOcFileSystem (&Root);
  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Could not find writable filesystem for virtualized dump - %r\n", Status));
    return;
  }

  Status = Root->Open (Root, &FileHandle, FileName, EFI_FILE_MODE_READ | EFI_FILE_MODE_WRITE, 0);
  if (!EFI_ERROR (Status)) {
    FileHandle->Delete (FileHandle);
  }

  Status = Root->Open (
                   Root,
                   &FileHandle,
                   FileName,
                   EFI_FILE_MODE_CREATE | EFI_FILE_MODE_WRITE | EFI_FILE_MODE_READ,
                   0
                   );

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Failed to create virtualized dump %s - %r\n", FileName, Status));
    Root->Close (Root);
    return;
  }

  //
  // Write the buffer to the file.
  //
  WriteSize = BufferSize;
  Status    = FileHandle->Write (FileHandle, &WriteSize, Buffer);

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: Failed to write to virtualized dump %s - %r\n", FileName, Status));
  } else {
    DEBUG ((DEBUG_INFO, "OC: Successfully dumped virtualized kernel to %s\n", FileName));
  }

  FileHandle->Close (FileHandle);
  Root->Close (Root);
}

STATIC
VOID
OcKernelConfigureCapabilities (
  IN OUT EFI_LOADED_IMAGE_PROTOCOL  *LoadedImage,
  IN     UINT32                     Capabilities
  )
{
  CONST CHAR8  *KernelArch;
  CHAR8        *AppleArchValue;
  CONST CHAR8  *NewArguments[2];
  UINT32       ArgumentCount;
  UINT32       RequestedArch;
  BOOLEAN      HasAppleArch;
  UINT32       KernelVersion;
  BOOLEAN      IsSnowLeo;
  BOOLEAN      IsLion;

  DEBUG ((DEBUG_VERBOSE, "OC: Supported boot capabilities %u\n", Capabilities));

  //
  // Reset to the default value.
  // Capabilities will always have K64 stripped when compiled for IA32.
  //
  mUse32BitKernel = (Capabilities & OC_KERN_CAPABILITY_K64_U64) == 0;

  //
  // Skip if not Apple image.
  //
  if (  (LoadedImage->FilePath == NULL)
     || ((OcGetBootDevicePathType (LoadedImage->FilePath, NULL, NULL) & OC_BOOT_APPLE_ANY) == 0))
  {
    return;
  }

  //
  // arch boot argument overrides any compatibility checks.
  //
  HasAppleArch = OcCheckArgumentFromEnv (
                   LoadedImage,
                   gRT->GetVariable,
                   "arch=",
                   L_STR_LEN ("arch="),
                   &AppleArchValue
                   );

  if (HasAppleArch) {
    mUse32BitKernel = AsciiStrCmp (AppleArchValue, "i386") == 0;
    DEBUG ((DEBUG_INFO, "OC: Arch %a overrides capabilities %u\n", AppleArchValue, Capabilities));
    FreePool (AppleArchValue);
    return;
  }

  //
  // Determine the current operating system.
  //
  IsSnowLeo = FALSE;
  IsLion    = FALSE;

  if ((Capabilities & OC_KERN_CAPABILITY_ALL) == OC_KERN_CAPABILITY_ALL) {
    KernelVersion = KERNEL_VERSION_SNOW_LEOPARD_MIN;
    IsSnowLeo     = TRUE;
  } else if ((Capabilities & OC_KERN_CAPABILITY_ALL) == OC_KERN_CAPABILITY_K32_K64_U64) {
    KernelVersion = KERNEL_VERSION_LION_MIN;
    IsLion        = TRUE;
  } else if ((Capabilities & OC_KERN_CAPABILITY_ALL) == OC_KERN_CAPABILITY_K32_U32_U64) {
    KernelVersion = KERNEL_VERSION_LEOPARD_MIN;
  } else {
    KernelVersion = KERNEL_VERSION_MOUNTAIN_LION_MIN;
  }

  //
  // Determine requested arch.
  //
  // There are issues with booting with -legacy on 10.4 and 10.5, and EFI64.
  // We can only use this on 10.6, or on 10.4/10.5 if on EFI32.
  //
  // i386-user32 is not supported on 10.7, fallback to i386.
  //
  KernelArch = OC_BLOB_GET (&mOcConfiguration->Kernel.Scheme.KernelArch);
  if (AsciiStrCmp (KernelArch, "x86_64") == 0) {
    RequestedArch = OC_KERN_CAPABILITY_K64_U64;
  } else if (AsciiStrCmp (KernelArch, "i386") == 0) {
    RequestedArch = OC_KERN_CAPABILITY_K32_U64;
  } else if (  AsciiStrCmp (KernelArch, "i386-user32") == 0
 #if defined (MDE_CPU_X64)
            && (IsSnowLeo || IsLion)
 #endif
               )
  {
    if (!IsLion) {
      RequestedArch = OC_KERN_CAPABILITY_K32_U32;
    } else {
      DEBUG ((DEBUG_INFO, "OC: Requested arch i386-user32 is not supported on 10.7, falling back to i386\n"));
      RequestedArch = OC_KERN_CAPABILITY_K32_U64;
    }
  } else {
    RequestedArch = 0;
  }

  //
  // In automatic mode, if we do not support SSSE3 and can downgrade to U32, do it.
  // See also note above regarding 10.4 and 10.5.
  //
  if (  RequestedArch == 0
 #if defined (MDE_CPU_X64)
     && IsSnowLeo
 #endif
     && (mOcCpuInfo->ExtFeatures & CPUID_EXTFEATURE_EM64T) != 0
     && (mOcCpuInfo->Features & CPUID_FEATURE_SSSE3) == 0
     && (Capabilities & OC_KERN_CAPABILITY_K32_U32) != 0)
  {
    //
    // Should be guaranteed that we support 32-bit kernel with a 64-bit userspace.
    //
    ASSERT ((Capabilities & OC_KERN_CAPABILITY_K32_U64) != 0);

    DEBUG ((DEBUG_INFO, "OC: Missing SSSE3 disables U64 capabilities %u\n", Capabilities));
    Capabilities = OC_KERN_CAPABILITY_K32_U32;
  }

  //
  // If we support K64 mode, check whether the board supports it.
  //
  if (  ((Capabilities & OC_KERN_CAPABILITY_K64_U64) != 0)
     && !OcPlatformIs64BitSupported (KernelVersion))
  {
    DEBUG ((DEBUG_INFO, "OC: K64 forbidden due to current platform on version %u\n", KernelVersion));
    Capabilities &= ~(OC_KERN_CAPABILITY_K64_U64);
  }

  //
  // If we are not choosing the architecture automatically, try to use the requested one.
  // Otherwise try best available.
  //
  if ((RequestedArch != 0) && ((Capabilities & RequestedArch) != 0)) {
    Capabilities = RequestedArch;
  } else if ((Capabilities & OC_KERN_CAPABILITY_K64_U64) != 0) {
    Capabilities = OC_KERN_CAPABILITY_K64_U64;
  } else if ((Capabilities & OC_KERN_CAPABILITY_K32_U64) != 0) {
    Capabilities = OC_KERN_CAPABILITY_K32_U64;
  } else if ((Capabilities & OC_KERN_CAPABILITY_K32_U32) != 0) {
    Capabilities = OC_KERN_CAPABILITY_K32_U32;
  } else {
    ASSERT (FALSE);
  }

  //
  // Pass arch argument when we are:
  // - SnowLeo64 and try to boot x86_64.
  // - SnowLeo64 or Lion64 and try to boot i386.
  //
  ArgumentCount = 0;
  if ((Capabilities == OC_KERN_CAPABILITY_K64_U64) && IsSnowLeo) {
    NewArguments[ArgumentCount++] = "arch=x86_64";
  } else if ((Capabilities != OC_KERN_CAPABILITY_K64_U64) && (IsSnowLeo || IsLion)) {
    NewArguments[ArgumentCount++] = "arch=i386";
  }

  //
  // Pass legacy argument when we are booting i386.
  //
  if (  (Capabilities == OC_KERN_CAPABILITY_K32_U32)
     && !OcCheckArgumentFromEnv (LoadedImage, gRT->GetVariable, "-legacy", L_STR_LEN ("-legacy"), NULL))
  {
    NewArguments[ArgumentCount++] = "-legacy";
  }

  //
  // Update argument list.
  //
  if (ArgumentCount > 0) {
    OcAppendArgumentsToLoadedImage (
      LoadedImage,
      &NewArguments[0],
      ArgumentCount,
      FALSE
      );
  }

  //
  // If we do not support K64 for this target, force 32.
  //
  if ((Capabilities & OC_KERN_CAPABILITY_K64_U64) == 0) {
    mUse32BitKernel = TRUE;
  }
}

STATIC
VOID
OcKernelLoadAndReserveKext (
  IN     OC_KERNEL_ADD_ENTRY  *Kext,
  IN     UINT32               Index,
  IN     BOOLEAN              IsForced,
  IN     EFI_FILE_PROTOCOL    *RootFile,
  IN     OC_STORAGE_CONTEXT   *Storage,
  IN     OC_GLOBAL_CONFIG     *Config,
  IN     KERNEL_CACHE_TYPE    CacheType,
  IN     BOOLEAN              Is32Bit,
  IN OUT UINT32               *ReservedExeSize,
  IN OUT UINT32               *ReservedInfoSize,
  IN OUT UINT32               *NumReservedKexts
  )
{
  EFI_STATUS   Status;
  CHAR8        *Identifier;
  CHAR8        *BundlePath;
  CHAR8        *Comment;
  CONST CHAR8  *Arch;
  CHAR8        *PlistPath;
  CHAR8        *ExecutablePath;
  CHAR16       FullPath[OC_STORAGE_SAFE_PATH_MAX];

  if (!Kext->Enabled) {
    return;
  }

  //
  // Free existing data if present, but only for forced kexts.
  // Injected kexts will never change.
  //
  if (IsForced && (Kext->PlistData != NULL)) {
    FreePool (Kext->PlistData);
    Kext->PlistDataSize = 0;
    Kext->PlistData     = NULL;

    if (Kext->ImageData != NULL) {
      FreePool (Kext->ImageData);
      Kext->ImageDataSize = 0;
      Kext->ImageData     = NULL;
    }
  }

  Identifier = OC_BLOB_GET (&Kext->Identifier);
  BundlePath = OC_BLOB_GET (&Kext->BundlePath);
  Comment    = OC_BLOB_GET (&Kext->Comment);
  Arch       = OC_BLOB_GET (&Kext->Arch);
  PlistPath  = OC_BLOB_GET (&Kext->PlistPath);
  if ((BundlePath[0] == '\0') || (PlistPath[0] == '\0') || (IsForced && (Identifier[0] == '\0'))) {
    DEBUG ((
      DEBUG_ERROR,
      "OC: %s kext %u (%a) has invalid info\n",
      IsForced ? L"Forced" : L"Injected",
      Index,
      Comment
      ));
    Kext->Enabled = FALSE;
    return;
  }

  if (AsciiStrCmp (Arch, Is32Bit ? "x86_64" : "i386") == 0) {
    DEBUG ((
      DEBUG_INFO,
      "OC: %s kext %a (%a) at %u skipped due to arch %a != %a\n",
      IsForced ? L"Forced" : L"Injected",
      BundlePath,
      Comment,
      Index,
      Arch,
      Is32Bit ? "i386" : "x86_64"
      ));
    return;
  }

  //
  // Required for possible cacheless force injection later on.
  //
  AsciiUefiSlashes (BundlePath);

  //
  // Get plist path and data.
  //
  Status = OcUnicodeSafeSPrint (
             FullPath,
             sizeof (FullPath),
             IsForced ? L"%a\\%a" : OPEN_CORE_KEXT_PATH "%a\\%a",
             BundlePath,
             PlistPath
             );
  if (EFI_ERROR (Status)) {
    DEBUG ((
      DEBUG_WARN,
      "OC: Failed to fit %s kext path %s%a\\%a",
      IsForced ? L"forced" : L"injected",
      IsForced ? L"" : OPEN_CORE_KEXT_PATH,
      BundlePath,
      PlistPath
      ));
    Kext->Enabled = IsForced;
    return;
  }

  UnicodeUefiSlashes (FullPath);

  if (IsForced) {
    Kext->PlistData = OcReadFileFromDirectory (
                        RootFile,
                        FullPath,
                        &Kext->PlistDataSize,
                        0
                        );
  } else {
    Kext->PlistData = OcStorageReadFileUnicode (
                        Storage,
                        FullPath,
                        &Kext->PlistDataSize
                        );
  }

  if (Kext->PlistData == NULL) {
    DEBUG ((
      IsForced ? DEBUG_INFO : DEBUG_ERROR,
      "OC: Plist %s is missing for %s kext %a (%a)\n",
      FullPath,
      IsForced ? L"forced" : L"injected",
      BundlePath,
      Comment
      ));
    Kext->Enabled = IsForced;
    return;
  }

  //
  // Get executable path and data, if present.
  //
  ExecutablePath = OC_BLOB_GET (&Kext->ExecutablePath);
  if (ExecutablePath[0] != '\0') {
    Status = OcUnicodeSafeSPrint (
               FullPath,
               sizeof (FullPath),
               IsForced ? L"%a\\%a" : OPEN_CORE_KEXT_PATH "%a\\%a",
               BundlePath,
               ExecutablePath
               );
    if (EFI_ERROR (Status)) {
      DEBUG ((
        DEBUG_WARN,
        "OC: Failed to fit %s kext path %s%a\\%a",
        IsForced ? L"forced" : L"injected",
        IsForced ? L"" : OPEN_CORE_KEXT_PATH,
        BundlePath,
        ExecutablePath
        ));
      Kext->Enabled = IsForced;
      FreePool (Kext->PlistData);
      Kext->PlistData = NULL;
      return;
    }

    UnicodeUefiSlashes (FullPath);

    if (IsForced) {
      Kext->ImageData = OcReadFileFromDirectory (
                          RootFile,
                          FullPath,
                          &Kext->ImageDataSize,
                          0
                          );
    } else {
      Kext->ImageData = OcStorageReadFileUnicode (
                          Storage,
                          FullPath,
                          &Kext->ImageDataSize
                          );
    }

    if (Kext->ImageData == NULL) {
      DEBUG ((
        IsForced ? DEBUG_INFO : DEBUG_ERROR,
        "OC: Image %s is missing for %s kext %a (%a)\n",
        FullPath,
        IsForced ? L"forced" : L"injected",
        BundlePath,
        Comment
        ));
      Kext->Enabled = IsForced;
      FreePool (Kext->PlistData);
      Kext->PlistData = NULL;
      return;
    }
  }

  if ((CacheType == CacheTypeCacheless) || (CacheType == CacheTypeMkext)) {
    Status = MkextReserveKextSize (
               ReservedInfoSize,
               ReservedExeSize,
               Kext->PlistDataSize,
               Kext->ImageData,
               Kext->ImageDataSize,
               Is32Bit
               );
  } else if (CacheType == CacheTypePrelinked) {
    Status = PrelinkedReserveKextSize (
               ReservedInfoSize,
               ReservedExeSize,
               Kext->PlistDataSize,
               Kext->ImageData,
               Kext->ImageDataSize,
               Is32Bit
               );
  }

  if (EFI_ERROR (Status)) {
    DEBUG ((
      DEBUG_INFO,
      "OC: Failed to fit %s kext %a (%a) - %r\n",
      Is32Bit ? L"32-bit" : L"64-bit",
      BundlePath,
      Comment,
      Status
      ));
    if (Kext->ImageData != NULL) {
      FreePool (Kext->ImageData);
      Kext->ImageData = NULL;
    }

    FreePool (Kext->PlistData);
    Kext->PlistData = NULL;
    return;
  }

  (*NumReservedKexts)++;
}

STATIC
EFI_STATUS
OcKernelLoadKextsAndReserve (
  IN  EFI_FILE_PROTOCOL   *RootFile,
  IN  OC_STORAGE_CONTEXT  *Storage,
  IN  OC_GLOBAL_CONFIG    *Config,
  IN  KERNEL_CACHE_TYPE   CacheType,
  IN  BOOLEAN             Is32Bit,
  OUT UINT32              *ReservedExeSize,
  OUT UINT32              *ReservedInfoSize,
  OUT UINT32              *NumReservedKexts
  )
{
  UINT32               Index;
  OC_KERNEL_ADD_ENTRY  *Kext;

  *ReservedInfoSize = PRELINK_INFO_RESERVE_SIZE;
  *ReservedExeSize  = 0;
  *NumReservedKexts = 0;

  //
  // Process system kexts to be force injected.
  //
  for (Index = 0; Index < Config->Kernel.Force.Count; Index++) {
    Kext = Config->Kernel.Force.Values[Index];

    OcKernelLoadAndReserveKext (
      Kext,
      Index,
      TRUE,
      RootFile,
      Storage,
      Config,
      CacheType,
      Is32Bit,
      ReservedExeSize,
      ReservedInfoSize,
      NumReservedKexts
      );
  }

  //
  // Process kexts to be injected.
  //
  for (Index = 0; Index < Config->Kernel.Add.Count; Index++) {
    Kext = Config->Kernel.Add.Values[Index];

    OcKernelLoadAndReserveKext (
      Kext,
      Index,
      FALSE,
      RootFile,
      Storage,
      Config,
      CacheType,
      Is32Bit,
      ReservedExeSize,
      ReservedInfoSize,
      NumReservedKexts
      );
  }

  if (CacheType == CacheTypePrelinked) {
    if (  (*ReservedExeSize > PRELINKED_KEXTS_MAX_SIZE)
       || (*ReservedInfoSize + *ReservedExeSize < *ReservedExeSize))
    {
      return EFI_UNSUPPORTED;
    }
  }

  DEBUG ((
    DEBUG_INFO,
    "OC: Kext reservation size info %X exe %X\n",
    *ReservedInfoSize,
    *ReservedExeSize
    ));
  return EFI_SUCCESS;
}

STATIC
VOID
OcKernelInjectKext (
  IN OC_KERNEL_ADD_ENTRY  *Kext,
  IN UINT32               Index,
  IN BOOLEAN              IsForced,
  IN KERNEL_CACHE_TYPE    CacheType,
  IN VOID                 *Context,
  IN UINT32               DarwinVersion,
  IN BOOLEAN              Is32Bit
  )
{
  EFI_STATUS   Status;
  CONST CHAR8  *Identifier;
  CONST CHAR8  *BundlePath;
  CONST CHAR8  *ExecutablePath;
  CONST CHAR8  *Comment;
  CHAR8        FullPath[OC_STORAGE_SAFE_PATH_MAX];
  UINT32       MaxKernel;
  UINT32       MinKernel;
  CHAR8        BundleVersion[MAX_INFO_BUNDLE_VERSION_KEY_SIZE];

  if (!Kext->Enabled || (Kext->PlistData == NULL)) {
    return;
  }

  Identifier = OC_BLOB_GET (&Kext->Identifier);
  BundlePath = OC_BLOB_GET (&Kext->BundlePath);
  Comment    = OC_BLOB_GET (&Kext->Comment);
  MaxKernel  = OcParseDarwinVersion (OC_BLOB_GET (&Kext->MaxKernel));
  MinKernel  = OcParseDarwinVersion (OC_BLOB_GET (&Kext->MinKernel));

  //
  // Assume no bundle version from the beginning.
  // 'v' will be printed in the message, and hence is omitted here.
  //
  AsciiStrCpyS (BundleVersion, MAX_INFO_BUNDLE_VERSION_KEY_SIZE, "ersion unavailable");

  if (!OcMatchDarwinVersion (DarwinVersion, MinKernel, MaxKernel)) {
    DEBUG ((
      DEBUG_INFO,
      "OC: %a%a injection skips %a (%a) kext at %u due to version %u <= %u <= %u\n",
      PRINT_KERNEL_CACHE_TYPE (CacheType),
      IsForced ? " force" : "",
      BundlePath,
      Comment,
      Index,
      MinKernel,
      DarwinVersion,
      MaxKernel
      ));
    return;
  }

  if (Kext->ImageData != NULL) {
    ExecutablePath = OC_BLOB_GET (&Kext->ExecutablePath);
  } else {
    ExecutablePath = NULL;
  }

  if (!IsForced) {
    Status = OcAsciiSafeSPrint (FullPath, sizeof (FullPath), "/Library/Extensions/%a", BundlePath);
    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_WARN, "OC: Failed to fit kext path /Library/Extensions/%a", BundlePath));
      return;
    }
  }

  if (CacheType == CacheTypeCacheless) {
    if (  IsForced
       && (AsciiStrnCmp (BundlePath, "System\\Library\\Extensions", L_STR_LEN ("System\\Library\\Extensions")) == 0))
    {
      Status = CachelessContextForceKext (Context, Identifier);
    } else {
      Status = CachelessContextAddKext (
                 Context,
                 Kext->PlistData,
                 Kext->PlistDataSize,
                 Kext->ImageData,
                 Kext->ImageDataSize,
                 BundleVersion
                 );
    }
  } else if (CacheType == CacheTypeMkext) {
    Status = MkextInjectKext (
               Context,
               IsForced ? Identifier : NULL,
               IsForced ? BundlePath : FullPath,
               Kext->PlistData,
               Kext->PlistDataSize,
               Kext->ImageData,
               Kext->ImageDataSize,
               BundleVersion
               );
  } else if (CacheType == CacheTypePrelinked) {
    Status = PrelinkedInjectKext (
               Context,
               IsForced ? Identifier : NULL,
               IsForced ? BundlePath : FullPath,
               Kext->PlistData,
               Kext->PlistDataSize,
               ExecutablePath,
               Kext->ImageData,
               Kext->ImageDataSize,
               BundleVersion
               );
  } else {
    Status = EFI_UNSUPPORTED;
  }

  DEBUG ((
    !IsForced && EFI_ERROR (Status) ? DEBUG_WARN : DEBUG_INFO,
    "OC: %a%a injection %a (%a) - %r\n",
    PRINT_KERNEL_CACHE_TYPE (CacheType),
    IsForced ? " force" : "",
    BundlePath,
    Comment,
    Status
    ));

  //
  // Report kext bundle version for DEBUG build.
  //
  DEBUG_CODE_BEGIN ();
  DEBUG ((
    !IsForced && EFI_ERROR (Status) ? DEBUG_WARN : DEBUG_INFO,
    "OC: %a%a injection %a v%a\n",
    PRINT_KERNEL_CACHE_TYPE (CacheType),
    IsForced ? " force" : "",
    BundlePath,
    BundleVersion
    ));

  DEBUG_CODE_END ();
}

VOID
OcKernelInjectKexts (
  IN OC_GLOBAL_CONFIG   *Config,
  IN KERNEL_CACHE_TYPE  CacheType,
  IN VOID               *Context,
  IN UINT32             DarwinVersion,
  IN BOOLEAN            Is32Bit,
  IN UINT32             LinkedExpansion,
  IN UINT32             ReservedExeSize
  )
{
  EFI_STATUS  Status;
  UINT32      Index;

  if (CacheType == CacheTypePrelinked) {
    Status = PrelinkedInjectPrepare (
               Context,
               LinkedExpansion,
               ReservedExeSize
               );
    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_WARN, "OC: Prelink inject prepare error - %r\n", Status));
      return;
    }
  }

  //
  // Process system kexts to be force injected.
  //
  for (Index = 0; Index < Config->Kernel.Force.Count; Index++) {
    OcKernelInjectKext (
      Config->Kernel.Force.Values[Index],
      Index,
      TRUE,
      CacheType,
      Context,
      DarwinVersion,
      Is32Bit
      );
  }

  //
  // Process kexts to be injected.
  //
  for (Index = 0; Index < Config->Kernel.Add.Count; Index++) {
    OcKernelInjectKext (
      Config->Kernel.Add.Values[Index],
      Index,
      FALSE,
      CacheType,
      Context,
      DarwinVersion,
      Is32Bit
      );
  }

  if ((CacheType == CacheTypeCacheless) || (CacheType == CacheTypeMkext)) {
    Status = EFI_SUCCESS;
  } else if (CacheType == CacheTypePrelinked) {
    DEBUG ((
      DEBUG_INFO,
      "OC: Prelink size %u kext offset %u reserved %u\n",
      ((PRELINKED_CONTEXT *)Context)->PrelinkedSize,
      ((PRELINKED_CONTEXT *)Context)->KextsFileOffset,
      ReservedExeSize
      ));

    ASSERT (
      ((PRELINKED_CONTEXT *)Context)->PrelinkedSize -
      ((PRELINKED_CONTEXT *)Context)->KextsFileOffset <= ReservedExeSize
      );

    Status = PrelinkedInjectComplete (Context);
  } else {
    Status = EFI_UNSUPPORTED;
  }

  if (EFI_ERROR (Status)) {
    DEBUG ((DEBUG_WARN, "OC: %a insertion error - %r\n", PRINT_KERNEL_CACHE_TYPE (CacheType), Status));
  }
}

EFI_STATUS
OcKernelProcessPrelinked (
  IN     OC_GLOBAL_CONFIG  *Config,
  IN     UINT32            DarwinVersion,
  IN     BOOLEAN           Is32Bit,
  IN OUT UINT8             *Kernel,
  IN     UINT32            *KernelSize,
  IN     UINT32            AllocatedSize,
  IN     UINT32            LinkedExpansion,
  IN     UINT32            ReservedExeSize
  )
{
  EFI_STATUS         Status;
  PRELINKED_CONTEXT  Context;

  Status = PrelinkedContextInit (&Context, Kernel, *KernelSize, AllocatedSize, Is32Bit);

  if (!EFI_ERROR (Status)) {

    //
    // Dump the buffer after context initialization but before any modifications.
    //
    OcKernelDumpBuffer (
      Kernel,
      *KernelSize,
      DUMP_TYPE_PREPROCESSED,
      KERNEL_TYPE_PRELINKED,
      DarwinVersion
      );
    
    OcKernelBlockKexts (Config, DarwinVersion, Is32Bit, CacheTypePrelinked, &Context);

    OcKernelInjectKexts (Config, CacheTypePrelinked, &Context, DarwinVersion, Is32Bit, LinkedExpansion, ReservedExeSize);

    OcKernelApplyPatches (Config, mOcCpuInfo, DarwinVersion, Is32Bit, CacheTypePrelinked, &Context, NULL, 0);

    *KernelSize = Context.PrelinkedSize;

    PrelinkedContextFree (&Context);
  }

  return Status;
}

STATIC
EFI_STATUS
OcKernelProcessMkext (
  IN     OC_GLOBAL_CONFIG  *Config,
  IN     UINT32            DarwinVersion,
  IN     BOOLEAN           Is32Bit,
  IN OUT UINT8             *Mkext,
  IN OUT UINT32            *MkextSize,
  IN     UINT32            AllocatedSize
  )
{
  EFI_STATUS     Status;
  MKEXT_CONTEXT  Context;

  Status = MkextContextInit (&Context, Mkext, *MkextSize, AllocatedSize);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  OcKernelBlockKexts (Config, DarwinVersion, Is32Bit, CacheTypeMkext, &Context);

  OcKernelInjectKexts (Config, CacheTypeMkext, &Context, DarwinVersion, Is32Bit, 0, 0);

  OcKernelApplyPatches (Config, mOcCpuInfo, DarwinVersion, Is32Bit, CacheTypeMkext, &Context, NULL, 0);

  MkextInjectPatchComplete (&Context);

  *MkextSize = Context.MkextSize;

  MkextContextFree (&Context);
  return Status;
}

STATIC
EFI_STATUS
OcKernelInitCacheless (
  IN     OC_GLOBAL_CONFIG   *Config,
  IN     CACHELESS_CONTEXT  *Context,
  IN     UINT32             DarwinVersion,
  IN     BOOLEAN            Is32Bit,
  IN     CHAR16             *FileName,
  IN     EFI_FILE_PROTOCOL  *ExtensionsDir,
  OUT EFI_FILE_PROTOCOL     **File
  )
{
  EFI_STATUS  Status;

  Status = CachelessContextInit (
             Context,
             FileName,
             ExtensionsDir,
             DarwinVersion,
             Is32Bit
             );
  if (EFI_ERROR (Status)) {
    return Status;
  }

  OcKernelBlockKexts (Config, DarwinVersion, Is32Bit, CacheTypeCacheless, Context);

  OcKernelInjectKexts (Config, CacheTypeCacheless, Context, DarwinVersion, Is32Bit, 0, 0);

  OcKernelApplyPatches (Config, mOcCpuInfo, DarwinVersion, Is32Bit, CacheTypeCacheless, Context, NULL, 0);

  return CachelessContextOverlayExtensionsDir (Context, File);
}

STATIC
EFI_STATUS
OcKernelReadAppleKernel (
  IN     EFI_FILE_PROTOCOL  *RootFile,
  IN     EFI_FILE_PROTOCOL  *KernelFile,
  IN     CHAR16             *FileName,
  IN     BOOLEAN            Is32Bit,
  IN OUT UINT32             *DarwinVersion,
  OUT UINT8                 **Kernel,
  OUT UINT32                *KernelSize,
  OUT UINT32                *AllocatedSize,
  OUT UINT32                *ReservedExeSize,
  OUT UINT32                *LinkedExpansion,
  OUT UINT8                 *Digest  OPTIONAL
  )
{
  EFI_STATUS  Status;
  BOOLEAN     Result;
  UINT32      DarwinVersionNew;
  BOOLEAN     IsKernel32Bit;

  UINT32  ReservedInfoSize;
  UINT32  NumReservedKexts;
  UINT32  ReservedFullSize;

  OcKernelLoadKextsAndReserve (
    RootFile,
    mOcStorage,
    mOcConfiguration,
    CacheTypePrelinked,
    Is32Bit,
    ReservedExeSize,
    &ReservedInfoSize,
    &NumReservedKexts
    );

  *LinkedExpansion = KcGetSegmentFixupChainsSize (*ReservedExeSize);
  if (*LinkedExpansion == 0) {
    return EFI_UNSUPPORTED;
  }

  Result = BaseOverflowTriAddU32 (
             ReservedInfoSize,
             *ReservedExeSize,
             *LinkedExpansion,
             &ReservedFullSize
             );
  if (Result) {
    return EFI_UNSUPPORTED;
  }

  //
  // Read last requested architecture for kernel.
  //
  DEBUG ((DEBUG_INFO, "OC: Trying %a XNU hook on %s\n", Is32Bit ? "32-bit" : "64-bit", FileName));
  Status = ReadAppleKernel (
             KernelFile,
             Is32Bit,
             &IsKernel32Bit,
             Kernel,
             KernelSize,
             AllocatedSize,
             ReservedFullSize,
             Digest
             );
  DEBUG ((
    DEBUG_INFO,
    "OC: Result of %a XNU hook on %s (%02X%02X%02X%02X) is %r\n",
    IsKernel32Bit ? "32-bit" : "64-bit",
    FileName,
    Digest != NULL ? Digest[0] : 0,
    Digest != NULL ? Digest[1] : 0,
    Digest != NULL ? Digest[2] : 0,
    Digest != NULL ? Digest[3] : 0,
    Status
    ));

  if (!EFI_ERROR (Status)) {

    //
    // Scan for signatures to verify kernel contents.
    //
    OcTestAMDSignatures (*Kernel, *KernelSize);

    //
    // 10.6 and below may keep older prelinkedkernels around, do not load those.
    //
    DarwinVersionNew = OcKernelReadDarwinVersion (*Kernel, *KernelSize);
    if (DarwinVersionNew < *DarwinVersion) {
      FreePool (*Kernel);
      *Kernel = NULL;

      return EFI_INVALID_PARAMETER;
    }

    //
    // If we failed to obtain the requested bitness for the platform, abort.
    //
    if (Is32Bit != IsKernel32Bit) {
      DEBUG ((DEBUG_WARN, "OC: %a kernel architecture is not available, aborting.\n", Is32Bit ? "32-bit" : "64-bit"));
      FreePool (*Kernel);
      *Kernel = NULL;
      return EFI_NOT_FOUND;
    }

    *DarwinVersion = DarwinVersionNew;
  }

  return Status;
}

STATIC
EFI_STATUS
OcKernelFuzzyMatch (
  IN     EFI_FILE_PROTOCOL  *RootFile,
  IN     CHAR16             *FileName,
  IN     UINT64             OpenMode,
  IN     UINT64             Attributes,
  IN     BOOLEAN            Is32Bit,
  IN OUT UINT32             *DarwinVersion,
  OUT EFI_FILE_PROTOCOL     **KernelFile,
  OUT UINT8                 **Kernel,
  OUT UINT32                *KernelSize,
  OUT UINT32                *AllocatedSize,
  OUT UINT32                *ReservedExeSize,
  OUT UINT32                *LinkedExpansion,
  OUT UINT8                 *Digest  OPTIONAL
  )
{
  EFI_STATUS         Status;
  EFI_FILE_PROTOCOL  *FileDirectory;
  CHAR16             *FileNameDir;
  UINTN              FileNameDirLength;

  EFI_FILE_INFO  *FileInfo;
  EFI_FILE_INFO  *FileInfoNext;
  CHAR16         *FileNameCacheNew;
  UINTN          FileNameCacheNewLength;
  UINTN          FileNameCacheNewSize;

  DIRECTORY_SEARCH_CONTEXT  Context;

  FileInfo         = NULL;
  FileNameCacheNew = NULL;

  //
  // Open parent directory.
  //
  FileNameDirLength = OcStriStr (FileName, L"\\kernelcache") - FileName;
  FileNameDir       = AllocateZeroPool (StrnSizeS (FileName, FileNameDirLength));
  if (FileNameDir == NULL) {
    return EFI_OUT_OF_RESOURCES;
  }

  CopyMem (FileNameDir, FileName, StrnSizeS (FileName, FileNameDirLength) - sizeof (*FileName));

  Status = OcSafeFileOpen (RootFile, &FileDirectory, FileNameDir, EFI_FILE_MODE_READ, 0);
  if (EFI_ERROR (Status)) {
    FreePool (FileNameDir);
    return Status;
  }

  //
  // Search for kernelcache files, trying each one.
  //
  OcDirectorySeachContextInit (&Context);
  do {
    Status = OcGetNewestFileFromDirectory (
               &Context,
               FileDirectory,
               L"kernelcache",
               &FileInfoNext
               );

    if (EFI_ERROR (Status)) {
      break;
    }

    if (FileInfo != NULL) {
      FreePool (FileInfo);
    }

    if (FileNameCacheNew != NULL) {
      FreePool (FileNameCacheNew);
    }

    FileInfo = FileInfoNext;

    FileNameCacheNewLength = FileNameDirLength + L_STR_LEN ("\\") + StrLen (FileInfo->FileName);
    FileNameCacheNewSize   = (FileNameCacheNewLength + 1) * sizeof (*FileNameCacheNew);
    FileNameCacheNew       = AllocateZeroPool (FileNameCacheNewSize);
    if (FileNameCacheNew == NULL) {
      Status = EFI_OUT_OF_RESOURCES;
      break;
    }

    Status = OcUnicodeSafeSPrint (FileNameCacheNew, FileNameCacheNewSize, L"%s\\%s", FileNameDir, FileInfo->FileName);
    if (EFI_ERROR (Status)) {
      break;
    }

    Status = OcSafeFileOpen (RootFile, KernelFile, FileNameCacheNew, OpenMode, Attributes);
    if (EFI_ERROR (Status)) {
      continue;
    }

    Status = OcKernelReadAppleKernel (
               RootFile,
               *KernelFile,
               FileNameCacheNew,
               Is32Bit,
               DarwinVersion,
               Kernel,
               KernelSize,
               AllocatedSize,
               ReservedExeSize,
               LinkedExpansion,
               Digest
               );
  } while (EFI_ERROR (Status));

  if (FileInfo != NULL) {
    FreePool (FileInfo);
  }

  if (FileNameCacheNew != NULL) {
    FreePool (FileNameCacheNew);
  }

  FreePool (FileNameDir);

  return Status;
}

STATIC
EFI_STATUS
EFIAPI
OcKernelFileOpen (
  IN  EFI_FILE_PROTOCOL  *This,
  OUT EFI_FILE_PROTOCOL  **NewHandle,
  IN  CHAR16             *FileName,
  IN  UINT64             OpenMode,
  IN  UINT64             Attributes
  )
{
  EFI_STATUS         Status;
  BOOLEAN            Result;
  CONST CHAR8        *ForceCacheType;
  CONST CHAR8        *SecureBootModel;
  KERNEL_CACHE_TYPE  MaxCacheTypeAllowed;
  BOOLEAN            UseSecureBoot;

  UINT8              *Kernel;
  UINT32             KernelSize;
  UINT32             AllocatedSize;
  EFI_FILE_PROTOCOL  *VirtualFileHandle;
  EFI_STATUS         PrelinkedStatus;
  EFI_TIME           ModificationTime;
  UINT32             ReservedInfoSize;
  UINT32             ReservedExeSize;
  UINT32             NumReservedKexts;
  UINT32             LinkedExpansion;
  UINT32             ReservedFullSize;
  CHAR16             *NewFileName;
  EFI_FILE_PROTOCOL  *EspNewHandle;
  KERNEL_TYPE        CurrentKernelType;

  if (mCustomKernelDirectoryInProgress) {
    DEBUG ((DEBUG_INFO, "OC: Skipping OpenFile hooking on ESP Kernels directory\n"));
    return OcSafeFileOpen (This, NewHandle, FileName, OpenMode, Attributes);
  }

  //
  // Prevent access to cache files depending on maximum cache type allowed.
  //
  ForceCacheType = OC_BLOB_GET (&mOcConfiguration->Kernel.Scheme.KernelCache);
  if (AsciiStrCmp (ForceCacheType, "Cacheless") == 0) {
    MaxCacheTypeAllowed = CacheTypeCacheless;
  } else if (AsciiStrCmp (ForceCacheType, "Mkext") == 0) {
    MaxCacheTypeAllowed = CacheTypeMkext;
  } else if (AsciiStrCmp (ForceCacheType, "Prelinked") == 0) {
    MaxCacheTypeAllowed = CacheTypePrelinked;
  } else {
    MaxCacheTypeAllowed = CacheTypeNone;
  }

  //
  // We only want to calculate kernel hashes if secure boot is enabled.
  //
  SecureBootModel = OC_BLOB_GET (&mOcConfiguration->Misc.Security.SecureBootModel);
  UseSecureBoot   = AsciiStrCmp (SecureBootModel, OC_SB_MODEL_DISABLED) != 0;

  //
  // Hook injected OcXXXXXXXX.kext reads from /S/L/E.
  //
  if (  mOcCachelessInProgress
     && (OpenMode == EFI_FILE_MODE_READ)
     && (StrnCmp (FileName, L"System\\Library\\Extensions\\Oc", L_STR_LEN (L"System\\Library\\Extensions\\Oc")) == 0))
  {
    Status = CachelessContextPerformInject (&mOcCachelessContext, FileName, NewHandle);
    DEBUG ((
      DEBUG_INFO,
      "OC: Hooking SLE injected file %s with %u mode gave - %r\n",
      FileName,
      (UINT32)OpenMode,
      Status
      ));

    return Status;
  }

  Status = OcSafeFileOpen (This, NewHandle, FileName, OpenMode, Attributes);

  DEBUG ((
    DEBUG_VERBOSE,
    "OC: Opening file %s with %u mode gave - %r\n",
    FileName,
    (UINT32)OpenMode,
    Status
    ));

  //
  // Hook kernelcache read attempts for fuzzy kernelcache matching.
  // Only hook if the desired kernelcache file does not exist.
  //
  Kernel = NULL;
  if (  mOcConfiguration->Kernel.Scheme.FuzzyMatch
     && (Status == EFI_NOT_FOUND)
     && (OpenMode == EFI_FILE_MODE_READ)
     && (StrStr (FileName, L"\\kernelcache") != NULL))
  {
    //
    // Change the target to the custom one if requested CustomKernel.
    //
    if (mCustomKernelDirectory != NULL) {
      DEBUG ((DEBUG_INFO, "OC: Redirecting %s to the custom one on ESP\n", FileName));
      NewFileName = OcStrrChr (FileName, L'\\');
      if (NewFileName == NULL) {
        NewFileName = FileName;
      }

      DEBUG ((DEBUG_INFO, "OC: Filename after redirection: %s\n", NewFileName));

      This     = mCustomKernelDirectory;
      FileName = NewFileName;
    }

    DEBUG ((DEBUG_INFO, "OC: Trying kernelcache fuzzy matching on %s\n", FileName));

    Status = OcKernelFuzzyMatch (
               This,
               FileName,
               OpenMode,
               Attributes,
               mUse32BitKernel,
               &mOcDarwinVersion,
               NewHandle,
               &Kernel,
               &KernelSize,
               &AllocatedSize,
               &ReservedExeSize,
               &LinkedExpansion,
               UseSecureBoot ? mKernelDigest : NULL
               );
  }

  if (EFI_ERROR (Status)) {
    return Status;
  }

  //
  // boot.efi uses /S/L/K/kernel as is to determine valid filesystem.
  // Just skip it to speedup the boot process.
  // On 10.9 mach_kernel is loaded for manual linking aferwards, so we cannot skip it.
  // We also want to skip files named "kernel" that are part of kext bundles, and im4m.
  //
  if (  (OpenMode == EFI_FILE_MODE_READ)
     && (OcStriStr (FileName, L"kernel") != NULL)
     && (StrCmp (FileName, L"System\\Library\\Kernels\\kernel") != 0)
     && (OcStriStr (FileName, L".kext\\") == NULL)
     && (OcStriStr (FileName, L".im4m") == NULL))
  {
    //
    // Change the target to the custom one if requested CustomKernel.
    //
    if (mCustomKernelDirectory != NULL) {
      if ((Attributes & EFI_FILE_DIRECTORY) != 0) {
        return OcSafeFileOpen (This, NewHandle, FileName, OpenMode, Attributes);
      }

      DEBUG ((DEBUG_INFO, "OC: boot.efi original requested path: %s\n", FileName));

      NewFileName = OcStrrChr (FileName, L'\\');
      if (NewFileName == NULL) {
        NewFileName = FileName;
      } else {
        NewFileName++;
      }

      DEBUG ((DEBUG_INFO, "OC: Attempting to open filename '%s' inside the Kernels directory.\n", NewFileName));

      mCustomKernelDirectoryInProgress = TRUE;
      Status                           = OcSafeFileOpen (mCustomKernelDirectory, &EspNewHandle, NewFileName, OpenMode, Attributes);
      mCustomKernelDirectoryInProgress = FALSE;

      DEBUG ((DEBUG_INFO, "OC: OcSafeFileOpen status: %r\n", Status));

      if (!EFI_ERROR (Status)) {
        DEBUG ((DEBUG_INFO, "OC: Custom kernel opened. Redirecting file handle.\n"));

        (*NewHandle)->Close (*NewHandle);

        This       = mCustomKernelDirectory;
        *NewHandle = EspNewHandle;
        FileName   = NewFileName;

        DEBUG ((DEBUG_INFO, "OC: Redirection is complete.\n"));
      } else {
        DEBUG ((DEBUG_WARN, "OC: Could not open custom kernel. Continuing with original path.\n"));
      }
    }

    //
    // Kernel loading for fuzzy kernelcache is performed earlier.
    //
    if (Kernel == NULL) {
      Status = OcKernelReadAppleKernel (
                 This,
                 *NewHandle,
                 FileName,
                 mUse32BitKernel,
                 &mOcDarwinVersion,
                 &Kernel,
                 &KernelSize,
                 &AllocatedSize,
                 &ReservedExeSize,
                 &LinkedExpansion,
                 UseSecureBoot ? mKernelDigest : NULL
                 );

      if (Status == EFI_NOT_FOUND) {
        (*NewHandle)->Close (*NewHandle);
        *NewHandle = NULL;

        return Status;
      }
    }

    if (!EFI_ERROR (Status)) {

      //
      // Dump kernel before patching.
      //
      if (  (OcStriStr (FileName, L"kernelcache") != NULL)
         || (OcStriStr (FileName, L"prelinkedkernel") != NULL))
      {
        CurrentKernelType = KERNEL_TYPE_PRELINKED;
        OcKernelDumpBuffer (Kernel, KernelSize, DUMP_TYPE_PREPATCHED, CurrentKernelType, mOcDarwinVersion);
      } else {
        CurrentKernelType = KERNEL_TYPE_PLAIN;
        OcKernelDumpBuffer (Kernel, KernelSize, DUMP_TYPE_PREPATCHED, CurrentKernelType, mOcDarwinVersion);
      }

      //
      // Disable prelinked if forcing mkext or cacheless, but only on appropriate versions.
      // We also disable prelinked on 10.5 or older due to prelinked on those versions being unsupported.
      //
      if (  ((OcStriStr (FileName, L"kernelcache") != NULL) || (OcStriStr (FileName, L"prelinkedkernel") != NULL))
         && (  ((MaxCacheTypeAllowed == CacheTypeNone) && (mOcDarwinVersion <= KERNEL_VERSION_LEOPARD_MAX))
            || ((MaxCacheTypeAllowed == CacheTypeMkext) && (mOcDarwinVersion <= KERNEL_VERSION_SNOW_LEOPARD_MAX))
            || ((MaxCacheTypeAllowed == CacheTypeCacheless) && (mOcDarwinVersion <= KERNEL_VERSION_MAVERICKS_MAX))))
      {
        DEBUG ((DEBUG_INFO, "OC: Blocking prelinked due to ForceKernelCache=%a: %s\n", ForceCacheType, FileName));

        FreePool (Kernel);
        (*NewHandle)->Close (*NewHandle);
        *NewHandle = NULL;

        return EFI_NOT_FOUND;
      }

      //
      // Scan for signatures to verify kernel contents.
      //
      OcTestAMDSignatures (Kernel, KernelSize);

      //
      // Apply patches to kernel itself, and then process prelinked.
      //
      OcKernelApplyPatches (
        mOcConfiguration,
        mOcCpuInfo,
        mOcDarwinVersion,
        mUse32BitKernel,
        CacheTypeNone,
        NULL,
        Kernel,
        KernelSize
        );

      // Dump modified buffer
      if (!EFI_ERROR (OcKernelApplyPatches)) {
        OcKernelDumpBuffer (Kernel, KernelSize, DUMP_TYPE_PATCHED, CurrentKernelType, mOcDarwinVersion);
      }

      PrelinkedStatus = OcKernelProcessPrelinked (
                          mOcConfiguration,
                          mOcDarwinVersion,
                          mUse32BitKernel,
                          Kernel,
                          &KernelSize,
                          AllocatedSize,
                          LinkedExpansion,
                          ReservedExeSize
                          );

      DEBUG ((DEBUG_INFO, "OC: Prelinked status - %r\n", PrelinkedStatus));

      Status = OcGetFileModificationTime (*NewHandle, &ModificationTime);
      if (EFI_ERROR (Status)) {
        ZeroMem (&ModificationTime, sizeof (ModificationTime));
      }

      (*NewHandle)->Close (*NewHandle);

      //
      // Virtualise newly created kernel.
      //
      Status = CreateVirtualFileFileNameCopy (FileName, Kernel, KernelSize, &ModificationTime, &VirtualFileHandle);
      if (EFI_ERROR (Status)) {
        DEBUG ((DEBUG_WARN, "OC: Failed to virtualise kernel file (%s) - %r\n", FileName, Status));
        FreePool (Kernel);
        return EFI_OUT_OF_RESOURCES;
      }

      OcDumpVirtualizedKernel (Kernel, KernelSize);

      //
      // Scan for signatures to verify kernel contents.
      //
      OcTestAMDSignatures (Kernel, KernelSize);

      if (UseSecureBoot) {
        OcAppleImg4RegisterOverride (mKernelDigest, Kernel, KernelSize);
      }

      //
      // Return our handle.
      //
      *NewHandle = VirtualFileHandle;
      return EFI_SUCCESS;
    }
  }

  if (  (OpenMode == EFI_FILE_MODE_READ)
     && (OcStriStr (FileName, L"Extensions.mkext") != NULL))
  {
    //
    // Disable mkext booting if forcing cacheless.
    //
    if (MaxCacheTypeAllowed == CacheTypeCacheless) {
      DEBUG ((DEBUG_INFO, "OC: Blocking mkext due to ForceKernelCache=%a: %s\n", ForceCacheType, FileName));
      (*NewHandle)->Close (*NewHandle);
      *NewHandle = NULL;

      return EFI_NOT_FOUND;
    }

    //
    // Dump kernel before patching.
    //
    OcKernelDumpBuffer (Kernel, KernelSize, DUMP_TYPE_PREPATCHED, KERNEL_TYPE_MKEXT, mOcDarwinVersion);

    OcKernelLoadKextsAndReserve (
      This,
      mOcStorage,
      mOcConfiguration,
      CacheTypeMkext,
      mUse32BitKernel,
      &ReservedExeSize,
      &ReservedInfoSize,
      &NumReservedKexts
      );

    Result = BaseOverflowAddU32 (
               ReservedInfoSize,
               ReservedExeSize,
               &ReservedFullSize
               );
    if (Result) {
      return EFI_UNSUPPORTED;
    }

    DEBUG ((DEBUG_INFO, "OC: Trying %a mkext hook on %s\n", mUse32BitKernel ? "32-bit" : "64-bit", FileName));
    Status = ReadAppleMkext (
               *NewHandle,
               mUse32BitKernel,
               &Kernel,
               &KernelSize,
               &AllocatedSize,
               ReservedFullSize,
               NumReservedKexts
               );
    DEBUG ((DEBUG_INFO, "OC: Result of mkext hook on %s is %r\n", FileName, Status));

    if (!EFI_ERROR (Status)) {
      //
      // Scan for signatures to verify kernel contents.
      //
      OcTestAMDSignatures (Kernel, KernelSize);

      //
      // Process mkext.
      //
      Status = OcKernelProcessMkext (
                 mOcConfiguration,
                 mOcDarwinVersion,
                 mUse32BitKernel,
                 Kernel,
                 &KernelSize,
                 AllocatedSize
                 );
      DEBUG ((DEBUG_INFO, "OC: Mkext status - %r\n", Status));

      if (!EFI_ERROR (Status)) {
        OcKernelDumpBuffer (Kernel, KernelSize, DUMP_TYPE_PATCHED, KERNEL_TYPE_MKEXT, mOcDarwinVersion);
      }

      if (!EFI_ERROR (Status)) {
        Status = OcGetFileModificationTime (*NewHandle, &ModificationTime);
        if (EFI_ERROR (Status)) {
          ZeroMem (&ModificationTime, sizeof (ModificationTime));
        }

        (*NewHandle)->Close (*NewHandle);

        //
        // Virtualise newly created mkext.
        //
        Status = CreateVirtualFileFileNameCopy (FileName, Kernel, KernelSize, &ModificationTime, &VirtualFileHandle);
        if (EFI_ERROR (Status)) {
          DEBUG ((DEBUG_WARN, "OC: Failed to virtualise mkext file (%s) - %r\n", FileName, Status));
          FreePool (Kernel);
          return EFI_OUT_OF_RESOURCES;
        }

        OcDumpVirtualizedKernel (Kernel, KernelSize);

        //
        // Scan for signatures to verify kernel contents.
        //
        OcTestAMDSignatures (Kernel, KernelSize);

        *NewHandle = VirtualFileHandle;
        return EFI_SUCCESS;
      } else {
        FreePool (Kernel);
      }
    }
  }

  //
  // Hook /S/L/E for cacheless boots.
  //
  if (  (OpenMode == EFI_FILE_MODE_READ)
     && (StrCmp (FileName, L"System\\Library\\Extensions") == 0))
  {
    //
    // Free existing context if we are re-opening Extensions directory.
    //
    if (mOcCachelessInProgress) {
      CachelessContextFree (&mOcCachelessContext);
    }

    mOcCachelessInProgress = FALSE;

    OcKernelLoadKextsAndReserve (
      This,
      mOcStorage,
      mOcConfiguration,
      CacheTypeCacheless,
      mUse32BitKernel,
      &ReservedExeSize,
      &ReservedInfoSize,
      &NumReservedKexts
      );

    //
    // Initialize Extensions directory overlay for cacheless injection.
    //
    Status = OcKernelInitCacheless (
               mOcConfiguration,
               &mOcCachelessContext,
               mOcDarwinVersion,
               mUse32BitKernel,
               FileName,
               *NewHandle,
               &VirtualFileHandle
               );

    DEBUG ((DEBUG_INFO, "OC: Result of SLE hook on %s is %r\n", FileName, Status));

    if (!EFI_ERROR (Status)) {
      mOcCachelessInProgress = TRUE;
      *NewHandle             = VirtualFileHandle;
      return EFI_SUCCESS;
    }
  }

  //
  // Hook /S/L/E contents for processing during cacheless boots.
  //
  if (  mOcCachelessInProgress
     && (OpenMode == EFI_FILE_MODE_READ)
     && (StrnCmp (FileName, L"System\\Library\\Extensions\\", L_STR_LEN (L"System\\Library\\Extensions\\")) == 0))
  {
    Status = CachelessContextHookBuiltin (
               &mOcCachelessContext,
               FileName,
               *NewHandle,
               &VirtualFileHandle
               );

    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_INFO, "OC: Error SLE hooking %s - %r\n", FileName, Status));
    }

    if (!EFI_ERROR (Status) && (VirtualFileHandle != NULL)) {
      *NewHandle = VirtualFileHandle;
      return EFI_SUCCESS;
    }
  }

  //
  // This is not Apple kernel, just return the original file.
  // We recurse the filtering to additionally catch com.apple.boot.[RPS] directories.
  //
  return CreateRealFile (*NewHandle, OcKernelFileOpen, TRUE, NewHandle);
}

VOID
OcLoadKernelSupport (
  IN OC_STORAGE_CONTEXT  *Storage,
  IN OC_GLOBAL_CONFIG    *Config,
  IN OC_CPU_INFO         *CpuInfo
  )
{
  EFI_STATUS         Status;
  EFI_FILE_PROTOCOL  *Root;

  Status = EnableVirtualFs (gBS, OcKernelFileOpen);

  if (!EFI_ERROR (Status)) {
    mOcStorage                       = Storage;
    mOcConfiguration                 = Config;
    mOcCpuInfo                       = CpuInfo;
    mOcDarwinVersion                 = 0;
    mOcCachelessInProgress           = FALSE;
    mCustomKernelDirectoryInProgress = FALSE;
    //
    // Open customised Kernels if needed.
    //
    mCustomKernelDirectory = NULL;
    if (mOcConfiguration->Kernel.Scheme.CustomKernel) {
      Status = OcFindWritableOcFileSystem (&Root);
      if (!EFI_ERROR (Status)) {
        //
        // Open Kernels directory.
        //
        Status = Root->Open (
                         Root,
                         &mCustomKernelDirectory,
                         L"Kernels",
                         EFI_FILE_MODE_READ,
                         EFI_FILE_DIRECTORY
                         );
        if (EFI_ERROR (Status)) {
          DEBUG ((DEBUG_INFO, "OC: Unable to open Kernels folder for custom kernel - %r, falling back to normal one\n", Status));
          mCustomKernelDirectory = NULL;
        }
      } else {
        DEBUG ((DEBUG_INFO, "OC: Unable to find root writable filesystem for custom kernel - %r, falling back to normal one\n", Status));
      }
    }

    OcImageLoaderRegisterConfigure (OcKernelConfigureCapabilities);
  } else {
    DEBUG ((DEBUG_ERROR, "OC: Failed to enable vfs - %r\n", Status));
  }
}

VOID
OcUnloadKernelSupport (
  VOID
  )
{
  EFI_STATUS  Status;

  if (mOcStorage != NULL) {
    OcImageLoaderRegisterConfigure (NULL);
    Status = DisableVirtualFs (gBS);
    if (EFI_ERROR (Status)) {
      DEBUG ((DEBUG_ERROR, "OC: Failed to disable vfs - %r\n", Status));
    }

    mOcStorage       = NULL;
    mOcConfiguration = NULL;
  }
}
