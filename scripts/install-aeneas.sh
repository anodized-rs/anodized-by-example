#!/usr/bin/env bash
set -euo pipefail
if [[ $# != 1 ]]; then
    echo "Usage: $0 <project-directory>" >&2
    exit 1
fi
project=$(cd "$1" && pwd)
verify="$project/anodized-verify-aeneas"
[[ -f "$project/Cargo.toml" && -f "$verify/lakefile.toml" ]] || {
    echo "Project must contain Cargo.toml and anodized-verify-aeneas/lakefile.toml: $project" >&2
    exit 1
}
tag=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' "$verify/lakefile.toml")
: "${tag:?no Aeneas revision in $verify/lakefile.toml}"
bundle="$verify/.aeneas"
asset=aeneas-$(uname -sm | tr 'A-Z ' 'a-z-' | sed 's/darwin/macos/; s/arm64/aarch64/').tar.gz
if [[ "$("$bundle/aeneas" -version 2>/dev/null || true)" != "aeneas $tag" ]] || [[ ! -x "$bundle/charon" ]]; then
    rm -rf "$bundle"
    mkdir -p "$bundle"
    curl -fsSL --proto '=https' "https://github.com/AeneasVerif/aeneas/releases/download/$tag/$asset" | tar -xz -C "$bundle"
fi
(cd "$bundle" && rustup toolchain install --no-self-update)
lean_toolchain="$verify/lean-toolchain"
if ! cmp -s "$lean_toolchain" "$bundle/backends/lean/lean-toolchain"; then
    echo 'Lean toolchain differs from the pinned Aeneas release; update lean-toolchain and lake-manifest.json.' >&2
    exit 1
fi
