# Clawristotle: Semi-Autonomous Mathematical Research

[![Lean Action CI](https://github.com/Vilin97/Clawristotle/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Vilin97/Clawristotle/actions/workflows/lean_action_ci.yml) [![arXiv](https://img.shields.io/badge/arXiv-2603.15929-b31b1b)](https://arxiv.org/abs/2603.15929) [![Paper](https://img.shields.io/badge/HF-Paper-yellow)](https://huggingface.co/papers/2603.15929) [![Logs](https://img.shields.io/badge/HF-Agent_Logs-yellow)](https://huggingface.co/datasets/Vilin97/Clawristotle-Logs)

Fully verified formalizations of research-level mathematics in Lean 4, achieved by a centaur team of AI agents and a human mathematician.

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

## Vlasov-Maxwell-Landau Steady-State Theorem

**Branch:** [`main`](https://github.com/Vilin97/Clawristotle/tree/main)

| Metric | Value |
|--------|-------|
| Status | 0 sorry's, 0 axioms |
| Lean 4 Code | 10,445 lines |
| Development Time | 10 days (Mar 1–10, 2026) |
| Estimated API Cost | ~$6,300 |

> **Theorem.** The only smooth positive steady states of the VML system with Coulomb collisions on T^3 are global Maxwellian equilibria, with E = 0 and B constant.

[arXiv:2603.15929](https://arxiv.org/abs/2603.15929) | [Agent Logs](https://huggingface.co/datasets/Vilin97/Clawristotle-Logs)

## The Team

- [Vasily Ilin](https://github.com/Vilin97) (Human): Architect & Reviewer
- [Claude Code](https://claude.com/claude-code) (Agent): Engineer & Prover
- [Aristotle](https://aristotle.harmonic.fun/) (ATP): Lemma Specialist
- [Gemini DeepThink](https://gemini.google.com) (Reasoning Model): Mathematician (VML only)

## License

[CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/)
