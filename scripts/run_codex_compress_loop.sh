#!/usr/bin/env bash
set -euo pipefail

REPO_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

if [[ -f "$REPO_DIR/.env" ]]; then
  set -a
  # shellcheck disable=SC1091
  source "$REPO_DIR/.env"
  set +a
fi

"$REPO_DIR/scripts/setup_codex_compress_home.sh" >/dev/null
exec python3.9 "$REPO_DIR/scripts/codex_compress_loop.py" "$@"
