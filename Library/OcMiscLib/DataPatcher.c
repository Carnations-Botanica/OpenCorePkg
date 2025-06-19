/** @file
  Copyright (C) 2019, vit9696. All rights reserved.

  All rights reserved.

  This program and the accompanying materials
  are licensed and made available under the terms and conditions of the BSD License
  which accompanies this distribution.  The full text of the license may be found at
  http://opensource.org/licenses/bsd-license.php

  THE PROGRAM IS DISTRIBUTED UNDER THE BSD LICENSE ON AN "AS IS" BASIS,
  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.
**/

#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/BaseOverflowLib.h>
#include <Library/DebugLib.h>
#include <Library/OcMiscLib.h>
#include <Library/PrintLib.h>

#define MAX_PRINTABLE_PATCH_SIZE  256

//
// Helper function to construct a hexadecimal string from a byte buffer.
// It formats the bytes into "XX YY ZZ " (with a trailing space) and stores them
// in the provided OutputBuffer. It ensures null-termination and removes any
// trailing space at the end of the constructed string.
//
STATIC
VOID
InternalConstructHexBytesString (
  IN CONST VOID  *Buffer,
  IN UINTN       BufferSize,
  OUT CHAR8      *OutputBuffer,
  IN UINTN       OutputBufferSize
  )
{
  CONST UINT8  *Bytes;
  UINTN        Index;
  UINTN        CurrentOffset;

  Bytes         = (CONST UINT8 *)Buffer;
  CurrentOffset = 0;

  for (Index = 0; Index < BufferSize && CurrentOffset + 3 <= OutputBufferSize; ++Index) {
    // Print 2 hexadecimal characters followed by a space.
    AsciiSPrint (&OutputBuffer[CurrentOffset], OutputBufferSize - CurrentOffset, "%02X ", Bytes[Index]);
    CurrentOffset += 3;
  }

  // Remove the last trailing space if it exists, and null-terminate the string.
  if ((CurrentOffset > 0) && (OutputBuffer[CurrentOffset - 1] == ' ')) {
    CurrentOffset--;
  }

  OutputBuffer[CurrentOffset] = '\0';
}

STATIC
BOOLEAN
InternalFindPattern (
  IN CONST UINT8   *Pattern,
  IN CONST UINT8   *PatternMask OPTIONAL,
  IN CONST UINT32  PatternSize,
  IN CONST UINT8   *Data,
  IN UINT32        DataSize,
  IN OUT UINT32    *DataOff
  )
{
  UINT32  Index;
  UINT32  LastOffset;
  UINT32  CurrentOffset;

  ASSERT (DataSize >= PatternSize);
  ASSERT (DataOff != NULL);

  if (PatternSize == 0) {
    return FALSE;
  }

  CurrentOffset = *DataOff;
  LastOffset    = DataSize - PatternSize;

  if (PatternMask == NULL) {
    while (CurrentOffset <= LastOffset) {
      for (Index = 0; Index < PatternSize; ++Index) {
        if (Data[CurrentOffset + Index] != Pattern[Index]) {
          break;
        }
      }

      if (Index == PatternSize) {
        *DataOff = CurrentOffset;
        return TRUE;
      }

      ++CurrentOffset;
    }
  } else {
    while (CurrentOffset <= LastOffset) {
      for (Index = 0; Index < PatternSize; ++Index) {
        if ((Data[CurrentOffset + Index] & PatternMask[Index]) != Pattern[Index]) {
          break;
        }
      }

      if (Index == PatternSize) {
        *DataOff = CurrentOffset;
        return TRUE;
      }

      ++CurrentOffset;
    }
  }

  return FALSE;
}

BOOLEAN
FindPattern (
  IN CONST UINT8   *Pattern,
  IN CONST UINT8   *PatternMask OPTIONAL,
  IN CONST UINT32  PatternSize,
  IN CONST UINT8   *Data,
  IN UINT32        DataSize,
  IN OUT UINT32    *DataOff
  )
{
  if (DataSize < PatternSize) {
    return FALSE;
  }

  return InternalFindPattern (
           Pattern,
           PatternMask,
           PatternSize,
           Data,
           DataSize,
           DataOff
           );
}

UINT32
ApplyPatch (
  IN CONST UINT8   *Pattern,
  IN CONST UINT8   *PatternMask OPTIONAL,
  IN CONST UINT32  PatternSize,
  IN CONST UINT8   *Replace,
  IN CONST UINT8   *ReplaceMask OPTIONAL,
  IN UINT8         *Data,
  IN UINT32        DataSize,
  IN UINT32        Count,
  IN UINT32        Skip
  )
{
  UINT32   ReplaceCount;
  UINT32   DataOff;
  BOOLEAN  Found;
  UINT8    OriginalLocationData[MAX_PRINTABLE_PATCH_SIZE];
  CHAR8    FormattedOriginalBytes[MAX_PRINTABLE_PATCH_SIZE * 3 + 1]; // 2 chars + 1 space per byte + null terminator
  CHAR8    FormattedPatchedBytes[MAX_PRINTABLE_PATCH_SIZE * 3 + 1];

  if (DataSize < PatternSize) {
    return 0;
  }

  // Warn if the patch size exceeds our debug print buffer capacity.
  if (PatternSize > MAX_PRINTABLE_PATCH_SIZE) {
    DEBUG ((DEBUG_WARN, "OC: Patch size (0x%X) exceeds debug print buffer size (0x%X), output will be truncated.\n", PatternSize, MAX_PRINTABLE_PATCH_SIZE));
  }

  ReplaceCount = 0;
  DataOff      = 0;

  while (TRUE) {
    Found = InternalFindPattern (
              Pattern,
              PatternMask,
              PatternSize,
              Data,
              DataSize,
              &DataOff
              );

    if (!Found) {
      break;
    }

    //
    // DataOff + PatternSize - 1 is guaranteed to be a valid offset here. As
    // DataSize can at most be MAX_UINT32, the maximum valid offset is
    // MAX_UINT32 - 1. In consequence, DataOff + PatternSize cannot wrap around.
    //

    //
    // Skip this finding if requested.
    //
    if (Skip > 0) {
      --Skip;
      DataOff += PatternSize;
      continue;
    }

    //
    // Store original bytes from the current location before modification.
    //
    CopyMem (OriginalLocationData, &Data[DataOff], MIN (PatternSize, MAX_PRINTABLE_PATCH_SIZE));
    DEBUG ((DEBUG_INFO, "OCAK: DataPatcher has been called:\n"));

    //
    // Perform replacement.
    //
    if (ReplaceMask == NULL) {
      CopyMem (&Data[DataOff], Replace, PatternSize);
    } else {
      for (UINTN Index = 0; Index < PatternSize; ++Index) {
        Data[DataOff + Index] = (Data[DataOff + Index] & ~ReplaceMask[Index]) | (Replace[Index] & ReplaceMask[Index]);
      }
    }

    //
    // Log detailed information about the applied patch in the desired format.
    // The InternalConstructHexBytesString function prepares the string,
    // and then a single DEBUG call prints the line without intermediate timestamps.
    //
    DEBUG ((
      DEBUG_INFO,
      "  Offset: 0x%08X\n",
      DataOff
      ));

    InternalConstructHexBytesString (
      OriginalLocationData,
      MIN (PatternSize, MAX_PRINTABLE_PATCH_SIZE),
      FormattedOriginalBytes,
      sizeof (FormattedOriginalBytes)
      );
    DEBUG ((DEBUG_INFO, "  Original: %a\n", FormattedOriginalBytes));

    InternalConstructHexBytesString (
      &Data[DataOff],
      MIN (PatternSize, MAX_PRINTABLE_PATCH_SIZE),
      FormattedPatchedBytes,
      sizeof (FormattedPatchedBytes)
      );
    DEBUG ((DEBUG_INFO, "  Patched:  %a\n", FormattedPatchedBytes));

    ++ReplaceCount;
    DataOff += PatternSize;

    //
    // Check replace count if requested.
    //
    if (Count > 0) {
      --Count;
      if (Count == 0) {
        break;
      }
    }
  }

  return ReplaceCount;
}
