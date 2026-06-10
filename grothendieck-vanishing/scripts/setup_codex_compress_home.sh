#!/usr/bin/env bash
set -euo pipefail

REPO_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
STATE_DIR="$REPO_DIR/.compress-state"
HOME_ROOT="${CODEX_COMPRESS_HOME_ROOT:-$STATE_DIR/codex-home}"
CODEX_DIR="$HOME_ROOT/.codex"
SOURCE_CODEX_DIR="${SOURCE_CODEX_DIR:-/mmfs1/home/vilin/.codex}"
LEAN_LSP_BIN="$REPO_DIR/.uv-tools/lean-lsp-mcp/bin/lean-lsp-mcp"

mkdir -p "$CODEX_DIR"

if [[ ! -x "$LEAN_LSP_BIN" ]]; then
  echo "lean-lsp-mcp not found at $LEAN_LSP_BIN" >&2
  exit 1
fi

if [[ ! -f "$CODEX_DIR/auth.json" ]]; then
  if [[ -f "$SOURCE_CODEX_DIR/auth.json" ]]; then
    cp "$SOURCE_CODEX_DIR/auth.json" "$CODEX_DIR/auth.json"
    chmod 600 "$CODEX_DIR/auth.json"
  else
    echo "Missing Codex auth.json in $CODEX_DIR and $SOURCE_CODEX_DIR" >&2
    exit 1
  fi
fi

cat > "$CODEX_DIR/config.toml" <<EOF
[projects."$REPO_DIR"]
trust_level = "trusted"

[mcp_servers.lean-lsp]
command = "/usr/bin/bash"
args = ["-lc", "cd $REPO_DIR && export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:\$PATH && export LEAN_PROJECT_PATH=$REPO_DIR && exec $LEAN_LSP_BIN --lean-project-path $REPO_DIR"]
EOF

echo "$HOME_ROOT"
