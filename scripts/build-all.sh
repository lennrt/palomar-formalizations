#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)

for project in "$repository_root"/zenodo-*/palomar; do
  echo "Building ${project#"$repository_root"/}"
  (cd "$project" && lake build)
done

echo "All Palomar Lake projects built successfully."
