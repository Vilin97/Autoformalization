#!/usr/bin/env bash
set -euo pipefail

REPO_DIR=/home/vilin/aristotle
LOG_DIR="$REPO_DIR/logs"
LOG_FILE="$LOG_DIR/aristotle-claude-prover.log"
LOCK_FILE="$LOG_DIR/aristotle-claude-prover.lock"
PROMPT="prove everything in this project. there cannot be any axioms or sorry's left, except FlasqueVanishing. do not stop until you are fully done"

export HOME=/home/vilin
export PATH=/home/vilin/.local/bin:/home/vilin/.nvm/versions/node/v22.22.1/bin:/usr/local/bin:/usr/bin:/bin

mkdir -p "$LOG_DIR"
exec 9>"$LOCK_FILE"

if ! flock -n 9; then
  printf '[%s] skip: previous claude prover run is still active\n' "$(date -Is)" >> "$LOG_FILE"
  exit 0
fi

{
  printf '\n[%s] starting claude prover run\n' "$(date -Is)"
  cd "$REPO_DIR"
  status=0
  /home/vilin/.local/bin/claude \
    --dangerously-skip-permissions \
    --no-session-persistence \
    -p "$PROMPT" || status=$?
  printf '[%s] claude exit status: %s\n' "$(date -Is)" "$status"
  exit "$status"
} >> "$LOG_FILE" 2>&1
