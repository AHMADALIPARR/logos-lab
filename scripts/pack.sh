#!/bin/sh
# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr
# Builds dist/logos-lab.tar.gz and dist/logos-lab.tar.gz.sha256 the same way every time:
# sorted names, fixed mtime, owner 0:0, gzip without a name or timestamp.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
DIST="$ROOT/dist"
MTIME=${PACK_MTIME:-2026-01-01 00:00:00Z}
export LC_ALL=C
mkdir -p "$DIST"
cd "$ROOT"
tar --sort=name --mtime="$MTIME" --owner=0 --group=0 --numeric-owner \
    --mode='u+rw,go+r,go-w' \
    --exclude=./.git --exclude=./dist \
    --transform='s,^\.,logos-lab,' \
    -cf - . | gzip -n -9 > "$DIST/logos-lab.tar.gz"
(cd "$DIST" && sha256sum logos-lab.tar.gz > logos-lab.tar.gz.sha256)
cat "$DIST/logos-lab.tar.gz.sha256"
