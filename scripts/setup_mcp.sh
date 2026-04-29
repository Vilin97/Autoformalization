#!/bin/bash
# Setup MCP servers (lean-lsp and aristotle-mcp) for Claude Code project scope.
#
# Usage:
#   ./scripts/setup_mcp.sh                    # install + configure
#   ./scripts/setup_mcp.sh --verify           # just verify existing setup
#
# Requirements: uv (https://docs.astral.sh/uv/)
#
# What this does:
#   1. Creates a .uv-tools/ venv for each MCP server (pip-installed)
#   2. Writes .mcp.json in the project root (project-scope Claude Code config)
#   3. Verifies both servers start correctly
#
# Environment:
#   ARISTOTLE_API_KEY  — required for aristotle-mcp (will prompt if missing)
#   LEAN_PROJECT_PATH  — auto-detected from script location if not set

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TOOLS_DIR="$PROJECT_ROOT/.uv-tools"

# ── Helpers ──────────────────────────────────────────────────────────────────

info()  { echo "  [INFO]  $*"; }
ok()    { echo "  [OK]    $*"; }
fail()  { echo "  [FAIL]  $*" >&2; }
die()   { fail "$@"; exit 1; }

# ── Detect lean toolchain path ───────────────────────────────────────────────

detect_lean_path() {
    # Prefer NVMe toolchain if available (much faster on GPFS clusters)
    if [[ -x /tmp/lean4-toolchain/bin/lean ]]; then
        echo "/tmp/lean4-toolchain/bin"
    elif command -v lean &>/dev/null; then
        dirname "$(command -v lean)"
    else
        echo ""
    fi
}

LEAN_BIN_DIR="$(detect_lean_path)"
LEAN_PROJECT_PATH="${LEAN_PROJECT_PATH:-$PROJECT_ROOT}"

# ── Check prerequisites ─────────────────────────────────────────────────────

check_prereqs() {
    command -v uv &>/dev/null || die "uv not found. Install: https://docs.astral.sh/uv/"
    if [[ -z "$LEAN_BIN_DIR" ]]; then
        fail "lean not found on PATH or at /tmp/lean4-toolchain/bin"
        fail "lean-lsp-mcp won't work without a lean toolchain"
    else
        ok "lean toolchain: $LEAN_BIN_DIR"
    fi
}

# ── Install a PyPI package into .uv-tools/<name> ────────────────────────────

install_tool() {
    local name="$1"
    local package="$2"  # PyPI name or git+https://... URL
    local venv="$TOOLS_DIR/$name"

    if [[ -d "$venv" ]] && [[ -x "$venv/bin/$name" ]]; then
        info "$name already installed at $venv/bin/$name"
        # Upgrade in-place
        uv pip install --python "$venv/bin/python" --upgrade "$package" 2>/dev/null || true
        return 0
    fi

    info "Installing $name from $package..."
    mkdir -p "$TOOLS_DIR"
    uv venv "$venv" --quiet 2>/dev/null
    uv pip install --python "$venv/bin/python" "$package" --quiet
    if [[ -x "$venv/bin/$name" ]]; then
        ok "$name installed at $venv/bin/$name"
    else
        die "$name binary not found after install"
    fi
}

# ── Write .mcp.json ─────────────────────────────────────────────────────────

write_mcp_json() {
    local lean_lsp_bin="$TOOLS_DIR/lean-lsp-mcp/bin/lean-lsp-mcp"
    local aristotle_bin="$TOOLS_DIR/aristotle-mcp/bin/aristotle-mcp"
    local mcp_json="$PROJECT_ROOT/.mcp.json"

    # Build PATH that includes lean toolchain
    local mcp_path="$LEAN_BIN_DIR"
    if [[ -d /tmp/lake-bin ]]; then
        mcp_path="/tmp/lake-bin:$mcp_path"
    fi

    # Aristotle API key
    local api_key="${ARISTOTLE_API_KEY:-}"
    if [[ -z "$api_key" ]]; then
        # Try .env file
        if [[ -f "$PROJECT_ROOT/.env" ]]; then
            api_key=$(grep -oP 'ARISTOTLE_API_KEY=\K.*' "$PROJECT_ROOT/.env" 2>/dev/null || true)
        fi
    fi
    if [[ -z "$api_key" ]]; then
        fail "ARISTOTLE_API_KEY not set (aristotle-mcp will fail without it)"
        fail "Set it in your environment or in $PROJECT_ROOT/.env"
    fi

    # Write the config
    cat > "$mcp_json" <<MCPEOF
{
  "mcpServers": {
    "lean-lsp": {
      "command": "$lean_lsp_bin",
      "args": [
        "--lean-project-path", "$LEAN_PROJECT_PATH"
      ],
      "env": {
        "PATH": "$mcp_path:\${PATH}"
      }
    },
    "aristotle": {
      "command": "$aristotle_bin",
      "env": {
        "ARISTOTLE_API_KEY": "$api_key"
      }
    }
  }
}
MCPEOF

    ok "Wrote $mcp_json"
}

# ── Verify servers start ────────────────────────────────────────────────────

verify_server() {
    local name="$1"
    local bin="$2"
    shift 2
    local args=("$@")

    info "Verifying $name..."

    # MCP stdio servers read JSON-RPC from stdin. Send an initialize request
    # and check we get a response. Timeout after 10s.
    local init_msg='{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"test","version":"0.1"}}}'

    local output
    if output=$(echo "$init_msg" | timeout 15 "$bin" "${args[@]}" 2>/dev/null); then
        if echo "$output" | grep -q '"result"' 2>/dev/null; then
            ok "$name responds to initialize"
            return 0
        fi
    fi

    # Some MCP servers need content-length framing
    local framed
    framed="Content-Length: ${#init_msg}\r\n\r\n${init_msg}"
    if output=$(printf '%s' "$framed" | timeout 15 "$bin" "${args[@]}" 2>/dev/null); then
        if echo "$output" | grep -q '"result"\|"serverInfo"' 2>/dev/null; then
            ok "$name responds to initialize (framed)"
            return 0
        fi
    fi

    fail "$name did not respond to initialize within 15s (may still work with Claude Code)"
    return 1
}

# ── Main ─────────────────────────────────────────────────────────────────────

main() {
    echo "=== MCP Server Setup for Claude Code ==="
    echo "Project: $PROJECT_ROOT"
    echo ""

    check_prereqs

    if [[ "${1:-}" == "--verify" ]]; then
        echo ""
        echo "── Verification only ──"
        verify_server "lean-lsp-mcp" "$TOOLS_DIR/lean-lsp-mcp/bin/lean-lsp-mcp" \
            --lean-project-path "$LEAN_PROJECT_PATH" || true
        verify_server "aristotle-mcp" "$TOOLS_DIR/aristotle-mcp/bin/aristotle-mcp" || true
        echo ""
        if [[ -f "$PROJECT_ROOT/.mcp.json" ]]; then
            ok ".mcp.json exists"
            cat "$PROJECT_ROOT/.mcp.json"
        else
            fail "No .mcp.json found"
        fi
        return
    fi

    echo ""
    echo "── Installing MCP servers ──"
    install_tool "lean-lsp-mcp" "lean-lsp-mcp"
    install_tool "aristotle-mcp" "aristotle-mcp @ git+https://github.com/Vilin97/aristotle-mcp"

    echo ""
    echo "── Writing .mcp.json ──"
    write_mcp_json

    echo ""
    echo "── Verifying ──"
    local all_ok=true
    verify_server "lean-lsp-mcp" "$TOOLS_DIR/lean-lsp-mcp/bin/lean-lsp-mcp" \
        --lean-project-path "$LEAN_PROJECT_PATH" || all_ok=false
    verify_server "aristotle-mcp" "$TOOLS_DIR/aristotle-mcp/bin/aristotle-mcp" || all_ok=false

    echo ""
    if $all_ok; then
        ok "All MCP servers configured and verified!"
    else
        info "Some servers could not be verified but may still work with Claude Code."
    fi
    echo ""
    echo "Final .mcp.json:"
    cat "$PROJECT_ROOT/.mcp.json"
}

main "$@"
