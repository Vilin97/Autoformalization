#!/usr/bin/env bash
# setup_local_cache.sh — Move .lake to local NVMe (/tmp) for fast olean access.
#
# GPFS (the /mmfs1 network filesystem) has high latency for small random reads.
# Lean loads ~8000 olean files on every compilation, making it 10-100x slower
# than on a local SSD. This script rsyncs .lake to node-local /tmp and symlinks
# it back, giving CI-like compile speeds.
#
# Idempotent: safe to call repeatedly. Resumable: rsync picks up where it left
# off if interrupted. Re-syncs from GPFS if the local cache is missing.
#
# Usage:
#   scripts/setup_local_cache.sh          # from repo root

set -euo pipefail

REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOCAL_CACHE="/tmp/aristotle-lake-$(id -u)"
LAKE_DIR="$REPO_DIR/.lake"

# Already set up and target exists?
if [ -L "$LAKE_DIR" ] && [ -d "$LOCAL_CACHE" ]; then
    echo "[cache] Local NVMe cache already active at $LOCAL_CACHE"
    exit 0
fi

# If .lake is a broken symlink (local cache was wiped), remove it and rebuild
if [ -L "$LAKE_DIR" ] && [ ! -d "$LOCAL_CACHE" ]; then
    echo "[cache] Stale symlink — local cache was wiped. Rebuilding from network..."
    rm "$LAKE_DIR"
    cd "$REPO_DIR"
    lake update 2>/dev/null || true
    lake exe cache get 2>/dev/null || true
    # Fall through to the rsync step below
fi

# If .lake is a real directory, rsync to /tmp and symlink
if [ -d "$LAKE_DIR" ] && [ ! -L "$LAKE_DIR" ]; then
    size="$(du -sh "$LAKE_DIR" 2>/dev/null | cut -f1)"
    echo "[cache] Syncing .lake ($size) to local NVMe ($LOCAL_CACHE)..."
    mkdir -p "$LOCAL_CACHE"
    rsync -a --delete "$LAKE_DIR/" "$LOCAL_CACHE/"
    rm -rf "$LAKE_DIR"
    ln -s "$LOCAL_CACHE" "$LAKE_DIR"
    echo "[cache] Done. .lake -> $LOCAL_CACHE"
    exit 0
fi

# Edge case: .lake doesn't exist at all
if [ ! -e "$LAKE_DIR" ]; then
    echo "[cache] No .lake found. Running lake update + cache get..."
    cd "$REPO_DIR"
    lake update 2>/dev/null || true
    lake exe cache get 2>/dev/null || true
    if [ -d "$LAKE_DIR" ]; then
        mkdir -p "$LOCAL_CACHE"
        rsync -a --delete "$LAKE_DIR/" "$LOCAL_CACHE/"
        rm -rf "$LAKE_DIR"
        ln -s "$LOCAL_CACHE" "$LAKE_DIR"
        echo "[cache] Done. .lake -> $LOCAL_CACHE"
    else
        echo "[cache] ERROR: lake did not create .lake directory" >&2
        exit 1
    fi
fi
