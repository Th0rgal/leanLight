# Design documents

leanLight was extracted from the light client of [leanKohakuDesktop](https://github.com/nconsigny/leanKohakuDesktop), a wallet whose repository is not public. Its design record and invariants are copied here so that the ids in leanLight's comments can be looked up.

| File | What it is |
|---|---|
| [`INVARIANTS.md`](INVARIANTS.md) | Rows 25a to 25l: what the code and proofs claim, the theorems behind each claim, and its status |
| [`spec-16-light-client.md`](spec-16-light-client.md) | The light client's design, verbatim: why, the protocol, the cryptography, anchored reads, and the decisions as they were taken. It also covers how the wallet runs the light client (`lkd-lc`, netd, Tor, the UI), which is not part of leanLight |

## Reading the ids in the comments

| Id | Meaning | Where |
|---|---|---|
| `25a` to `25l` | Invariant rows: 25a SSZ, 25b Merkleization, 25c BLS12-381, 25d chains, 25e bootstrap, 25f acceptance, 25g conflicts, 25h the age bound, 25i the clock, 25j EL binding, 25k facts, 25l inclusion | `INVARIANTS.md` |
| `G1` to `G19` | Goals, each compared with Helios | spec-16, "Why, and helios" |
| `H_vec`, `H_nonce` | Named hypotheses: what test vectors check and no proof covers | spec-16, "What remains trusted" |
| `LC0` to `LC9` | The milestones that built it | spec-16, "Milestones" |
| `D1` to `D60` | Design decisions | spec-16, "LC7 and LC8: the design as decided" (D1 to D37) and "LC9: the design as decided" (D38 on) |
| "open decision n" | Early decisions, with what was chosen | spec-16, "Open decisions, with recommendations" |

Module and namespace names in the documents are the wallet's: `LkdLc.X` is `LeanLight.X`, `LkdBase.X` is `LeanLight.Base.X`, `LkdProofs.Lc.X` is `LeanLightProofs.X`, and namespace `Lkd` is `LeanLight`.
