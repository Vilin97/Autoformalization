# Project Notes

The goal is not to end up with 0 sorry's! The goal is to make an honest formalization of the main theorem, with only the genuinely needed mathematical/physical assumptions. It is okay to have some sorry's laying around, as long as their statements are actually mathematically correct.

## Main file: `Aristotle/Landau/Theorem42.lean`

- The main theorem (`Theorem42`) must be stated cleanly at the end of the file with only the necessary mathematical hypotheses — no extra assumptions.
- Sorry's in the proof body are lemmas to be proved, not missing hypotheses.

## Files

Update these files after major changes:

- `progress.md` and `MEMORY.md` describe the project progress
- `critique.md` gives the critique of the current state, pointing to the weakest links
- `LOG.md` records session logs in reverse chronological order

## Proof style

- Decompose results into lemmas. Make lemmas more general than the specific result they serve — this is often easier to prove and leads to better design.
- Prefer `by sorry` for gaps that will be filled, not `axiom`.

## Aristotle workflow

See `/submit-aristotle` command for the full workflow, including error handling and common pitfalls.

Quick reference:
- Submit: `cd /home/vilin/aristotle && source .env && python3.10 Aristotle/Landau/check-aristotle.py submit aristotle-in/NAME.lean`
- Check: `cd /home/vilin/aristotle && source .env && python3.10 Aristotle/Landau/check-aristotle.py`
- Use `python3.10`, NOT `python` (default is 3.7, too old for aristotlelib).
- API key is in `.env`.

## Gemini

- For planning and reasoning tasks, especially requiring large context or heavy mathematical reasoning, call Gemini. Use `gemini-3.1-pro-preview`.

## Slash commands

All commands are defined in `.claude/commands/`. The full autonomous lifecycle is:

```
/babysit = /check-aristotle → /plan → /prove → /submit-aristotle → /simplify → /log → /cleanup → /critique → /commit
```

| Command | Purpose |
|---------|---------|
| `/check-aristotle` | Fetch and integrate completed Aristotle proofs |
| `/plan` | Assess state, classify issues, produce prioritized work plan |
| `/prove` | Close sorry's directly (decompose, define, prove) |
| `/submit-aristotle` | Prepare and submit hard lemmas to Aristotle |
| `/simplify` | Fix code smells, decompose long proofs, reduce heartbeats |
| `/log` | Record progress in LOG.md and update MEMORY.md |
| `/cleanup` | Delete stale Aristotle files and dead code |
| `/critique` | Adversarial analysis, write to critique.md |
| `/commit` | Build-verify, commit, and push |
| `/babysit` | Run the full lifecycle above in order |

## Building the project

Sometimes Lean decides to rebuild all Mathlib from scratch, which takes forever. If basic commands `lake build` take >30 seconds, that's why. In this case, run

1. `lake clean` to clean build outputs
2. `lake update` to update dependencies and save them to manifest
3. `lake exe cache get` to fetch Mathlib cache
4. `lake build` to ensure it worked

Also, sometimes the lean-lsp-mcp is being weird, you can run `lake build` for a more reliable output.
