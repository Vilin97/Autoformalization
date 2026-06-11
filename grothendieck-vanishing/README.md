# Grothendieck's Vanishing Theorem

> Part of [Clawristotle](../README.md), alongside [the Vlasov–Maxwell–Landau steady-state theorem](../landau/).

[![Grothendieck Vanishing CI](https://github.com/Vilin97/Clawristotle/actions/workflows/grothendieck-vanishing-ci.yml/badge.svg)](https://github.com/Vilin97/Clawristotle/actions/workflows/grothendieck-vanishing-ci.yml) [![Documentation](https://img.shields.io/badge/docs-blueprint-blue)](https://vilin97.github.io/Clawristotle/grothendieck-vanishing/blueprint/) [![Logs](https://img.shields.io/badge/HF-Agent_Logs-yellow)](https://huggingface.co/datasets/Vilin97/Clawristotle-Logs)

A fully verified formalization of Grothendieck's vanishing theorem in Lean 4, achieved by a centaur team of AI agents and human mathematicians.

> **Theorem.** For a Noetherian topological space X of dimension n and any sheaf F of abelian groups on X, H^i(X, F) = 0 for all i > n.

| Metric | Value |
|--------|-------|
| Status | 0 sorry's, 0 axioms (beyond `propext` / `Classical.choice` / `Quot.sound`) |
| Lean 4 Code | 5,061 raw lines / 4,087 normalized (15 files) |
| Timeline | 35 days elapsed (27 active), 2026-03-27 → 2026-05-01 |
| | — 9 active days proving (Mar 27 – Apr 4) |
| | — 8-day human review (Apr 8 – Apr 15) |
| | — 14 days review-driven refactor + compress (Apr 17 – May 1) |
| Estimated API Cost | ~$15,000 |

[Technical Report](TECHNICAL_REPORT_GV.md) | [Brian's Review](review.md) | [LOC History](artifacts/loc_history_gv.png) | [Sorry History](artifacts/sorry_history_gv.png)

## The Team

- [Vasily Ilin](https://github.com/Vilin97) (Human): Architect & infrastructure
- [Brian Nugent](https://github.com/brian-nugent) (Human): Theorem statement, proof reference, flasque-vanishing architecture, and code review (×2)
- [Claude Code](https://claude.com/claude-code) (Agent): Engineer, prover, and Codex-loop evaluator
- [Codex CLI](https://openai.com/codex) (Agent): Worker for the compress (86 cycles) and refactor (478 cycles) loops
- [Aristotle](https://aristotle.harmonic.fun/) (ATP): Lemma specialist (94 proving-phase submissions + Apr 27 infra burst)

## History

Developed March–May 2026 on the [`grothendieck-vanishing`](https://github.com/Vilin97/Clawristotle/tree/grothendieck-vanishing) branch and merged into `main` as this directory, with full history preserved.

## License

Released under the [Apache License 2.0](../LICENSE).
