#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/aeneas-pin.sh
asset=aeneas-$(uname -sm | tr 'A-Z ' 'a-z-' | sed 's/darwin/macos/; s/arm64/aarch64/').tar.gz
if [[ "$(.aeneas/aeneas -version 2>/dev/null || true)" != "aeneas $tag" ]] || [[ ! -x .aeneas/charon ]]; then
    rm -rf .aeneas
    mkdir -p .aeneas
    curl -fsSL --proto '=https' "https://github.com/AeneasVerif/aeneas/releases/download/$tag/$asset" | tar -xz -C .aeneas
fi
(cd .aeneas && rustup toolchain install --no-self-update)
if ! cmp -s lean-toolchain .aeneas/backends/lean/lean-toolchain; then
    echo 'Lean toolchain differs from the pinned Aeneas release; update lean-toolchain and lake-manifest.json.' >&2
    exit 1
fi
