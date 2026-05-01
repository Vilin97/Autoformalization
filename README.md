# Clawristotle: Semi-Autonomous Mathematical Research

[![Lean Action CI](https://github.com/Vilin97/Clawristotle/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Vilin97/Clawristotle/actions/workflows/lean_action_ci.yml) [![Logs](https://img.shields.io/badge/HF-Agent_Logs-yellow)](https://huggingface.co/datasets/Vilin97/Clawristotle-Logs)

A fully verified formalization of research-level mathematics in Lean 4, achieved by a centaur team of AI agents and a human mathematician.

## Grothendieck's Vanishing Theorem

**Branch:** [`grothendieck-vanishing`](https://github.com/Vilin97/Clawristotle/tree/grothendieck-vanishing)

| Metric | Value |
|--------|-------|
| Status | 0 sorry's, 0 axioms |
| Lean 4 Code | 5,844 lines |
| Development Time | 9 days (Mar 27 – Apr 4, 2026) |
| Estimated API Cost | ~$15,000 |

> **Theorem.** For a Noetherian topological space X of dimension n and any sheaf F of abelian groups on X, H^i(X, F) = 0 for all i > n.

[Technical Report](TECHNICAL_REPORT.md) | [LOC History](artifacts/loc_history_gv.png) | [Sorry History](artifacts/sorry_history_gv.png)

## The Team

- [Vasily Ilin](https://github.com/Vilin97) (Human): Architect & Reviewer
- [Brian Nugent](https://github.com/brian-nugent) (Human): Theorem statement, proof reference, flasque vanishing architecture
- [Claude Code](https://claude.com/claude-code) (Agent): Engineer & Prover
- [Aristotle](https://aristotle.harmonic.fun/) (ATP): Lemma Specialist

## License

[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/)
