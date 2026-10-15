# Source provenance

The edge-clique scalar argument follows Domagoj Bradač,
[*A generalization of Turán’s theorem* (2022), arXiv:2205.08923](https://arxiv.org/abs/2205.08923).
This is attribution for the mathematical argument. Motzkin–Straus lemmas are
adapted from Shengtong Zhang’s
[`BN/MS/Basic.lean`](https://github.com/ShengtongZhang-alt/BN/blob/5f4741254398424b730c9a893220a51e1cd829c5/BN/MS/Basic.lean).
The spectral transfer uses BN’s completely positive lift.

| Lean implementation | Role |
|---|---|
| `Transfer.lean` | Transfers a homogeneous scalar certificate through the BN completely positive lift using weighted Cauchy–Schwarz. |
| `LocalCliques.lean` | Defines the edge-clique number and reciprocal edge weights, and proves the nonedge transfer identity. |
| `ScalarCertificate.lean` | Implements support compression to a clique and proves the homogeneous edge-clique scalar certificate. |
| `Concrete.lean` | Applies the scalar certificate to the spectral transfer and converts the result to the unordered-edge bound for noncomplete graphs. |

| Source or dependency | Repository | Revision |
|---|---|---|
| Reused BN Lean proof source | [ShengtongZhang-alt/BN](https://github.com/ShengtongZhang-alt/BN/tree/5f4741254398424b730c9a893220a51e1cd829c5) | `5f4741254398424b730c9a893220a51e1cd829c5` |
| Mathlib dependency | leanprover-community/mathlib4 | `c55e6e786f49471c72fbddbec5415808896aec1e` |

The BN modules and adapted Motzkin–Straus source retain Shengtong Zhang’s
copyright and Apache-2.0 notices. The repository’s root `LICENSE` records the
Apache-2.0 terms.
