#!/usr/bin/env bash
set -euo pipefail

REPO_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

"$REPO_DIR/scripts/setup_codex_refactor_home.sh" >/dev/null
exec python3.9 "$REPO_DIR/scripts/codex_refactor_loop.py" "$@"
