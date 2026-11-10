#!/usr/bin/env bash
# Sourced from the repository root by the installer and translator.
tag=
lakefiles=("$@")
if [[ ${#lakefiles[@]} == 0 ]]; then
    lakefiles=(*/lakefile.toml)
fi
for lakefile in "${lakefiles[@]}"; do
    [[ -f "$lakefile" ]] || continue
    revision=$(awk -F'"' '/^\[/{name=""} /^name = /{name=$2} /^rev = / && name=="aeneas"{print $2}' "$lakefile")
    : "${revision:?no Aeneas revision in $lakefile}"
    if [[ -n "$tag" && "$tag" != "$revision" ]]; then
        echo "Aeneas revisions differ between example Lake projects." >&2
        return 1
    fi
    tag=$revision
done
: "${tag:?no example Lake projects found}"
