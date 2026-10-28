#!/bin/sh
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
find "$ROOT/objects/sha256" -type f | while IFS= read -r file; do
  expected=${file##*/}
  actual=$(sha256sum "$file" | cut -d ' ' -f 1)
  [ "$expected" = "$actual" ] || { echo "CORRUPT $file" >&2; exit 1; }
done
printf 'All stored object hashes verified\n'
