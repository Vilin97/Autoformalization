# Clawristotle: Semi-Autonomous Mathematical Research

<p align="center">
  <img src="landau/artifacts/clawristotle.png" alt="Clawristotle" width="400">
</p>

[![Landau CI](https://github.com/Vilin97/Clawristotle/actions/workflows/landau-ci.yml/badge.svg)](https://github.com/Vilin97/Clawristotle/actions/workflows/landau-ci.yml) [![Grothendieck Vanishing CI](https://github.com/Vilin97/Clawristotle/actions/workflows/grothendieck-vanishing-ci.yml/badge.svg)](https://github.com/Vilin97/Clawristotle/actions/workflows/grothendieck-vanishing-ci.yml) [![Website](https://img.shields.io/badge/docs-website-blue)](https://vilin97.github.io/Clawristotle/) [![Logs](https://img.shields.io/badge/HF-Agent_Logs-yellow)](https://huggingface.co/datasets/Vilin97/Clawristotle-Logs)

Fully verified formalizations of research-level mathematics in Lean 4, produced by centaur teams of AI agents and human mathematicians.

This repository hosts two completed formalization projects. Each is a self-contained Lean 4 / Mathlib package in its own directory, with its own toolchain, README, and technical report.

| | [`landau/`](landau/) | [`grothendieck-vanishing/`](grothendieck-vanishing/) |
|---|---|---|
| **Theorem** | Positive smooth steady states of the Vlasov–Maxwell–Landau system on 𝕋³ are global Maxwellians (Guo–Strain, Theorem 42) | For a Noetherian topological space X of dimension n and any sheaf F of abelian groups, Hⁱ(X, F) = 0 for i > n (Hartshorne III, 2.7) |
| **Status** | ✅ Fully verified, 0 `sorry`'s | ✅ Fully verified, 0 `sorry`'s, no extra axioms |
| **Lean 4 code** | 10,445 lines | 5,061 lines (4,087 normalized) |
| **Timeline** | 10 days (Mar 1–10, 2026) | 35 days (Mar 27 – May 1, 2026) |
| **API cost** | ~$6,300 | ~$15,000 |
| **Agents** | Claude Code · Gemini DeepThink · Aristotle | Claude Code · Codex CLI · Aristotle |
| **Paper** | [arXiv:2603.15929](https://arxiv.org/abs/2603.15929) · [HF paper](https://huggingface.co/papers/2603.15929) | [Technical report](grothendieck-vanishing/TECHNICAL_REPORT_GV.md) |
| **Read more** | [README](landau/README.md) · [Technical report](landau/TECHNICAL_REPORT.md) · [Blueprint](https://vilin97.github.io/Clawristotle/landau/blueprint/) | [README](grothendieck-vanishing/README.md) · [Brian's review](grothendieck-vanishing/review.md) · [Blueprint](https://vilin97.github.io/Clawristotle/grothendieck-vanishing/blueprint/) |

An additional project, [`mckay-conjecture/`](mckay-conjecture/), is in active
development. Its first milestone is a compiled, adversarially audited Lean
statement of the McKay conjecture for ordinary irreducible complex characters.

## How it works

The human steers — choosing the theorem, fixing the definitions, auditing the final statement — while AI agents handle the implementation: writing the Lean code, searching for proofs, dispatching hard lemmas to the [Aristotle](https://aristotle.harmonic.fun/) cloud prover, and reviewing their own output in autonomous critique–plan–prove–simplify loops. Each project's README describes its agent stack and how the method evolved between the two projects.

## Working in this repository

Each project is an independent Lake package with its own `lean-toolchain` — build from inside its directory:

```bash
cd landau                  # or grothendieck-vanishing
lake exe cache get         # fetch the Mathlib build cache
lake build
```

The Landau project was developed first, on this repository's `main` branch (March 2026); the Grothendieck vanishing project followed on the [`grothendieck-vanishing`](https://github.com/Vilin97/Clawristotle/tree/grothendieck-vanishing) branch (March–May 2026) and was merged into `main` with full history.

## License

Released under the [Apache License 2.0](LICENSE).
