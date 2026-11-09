#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
tag=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' lakefile.toml)
: "${tag:?no Aeneas revision in lakefile.toml}"
asset=aeneas-$(uname -sm | tr 'A-Z ' 'a-z-' | sed 's/darwin/macos/; s/arm64/aarch64/').tar.gz
if [[ "$(.aeneas/aeneas -version 2>/dev/null || true)" != "aeneas $tag" ]] || [[ ! -x .aeneas/charon ]]; then
    rm -rf .aeneas
    mkdir -p .aeneas
    curl -fsSL --proto '=https' "https://github.com/AeneasVerif/aeneas/releases/download/$tag/$asset" | tar -xz -C .aeneas
fi
# Some macOS release bundles refer to Nix-store libraries that are not shipped
# in the archive. Use the equivalent macOS system libraries and re-sign the
# modified executables (required on Apple Silicon).
if [[ $(uname -s) == Darwin ]]; then
    for binary in .aeneas/charon .aeneas/charon-driver; do
        changed=0
        while IFS= read -r lib; do
            case "$lib" in
                /nix/store/*/lib/libiconv.2.dylib) replacement=/usr/lib/libiconv.2.dylib ;;
                /nix/store/*/lib/libz.dylib) replacement=/usr/lib/libz.1.dylib ;;
                *) continue ;;
            esac
            install_name_tool -change "$lib" "$replacement" "$binary"
            changed=1
        done < <(otool -L "$binary" | awk 'NR > 1 {print $1}')
        if [[ $changed == 1 ]]; then
            codesign --force --sign - "$binary"
        fi
    done
fi
(cd .aeneas && rustup toolchain install --no-self-update)
if ! cmp -s lean-toolchain .aeneas/backends/lean/lean-toolchain; then
    echo 'Lean toolchain differs from the pinned Aeneas release; update lean-toolchain and lake-manifest.json.' >&2
    exit 1
fi
