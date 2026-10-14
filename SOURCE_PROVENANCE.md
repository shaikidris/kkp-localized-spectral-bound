# Source provenance

This package contains substantive proof source. Its authoritative submission
snapshot is the exact clean commit selected for verification and intake. The exact source roles are:

| Role | Repository | Commit |
|---|---|---|
| Extracted BN proof source | ShengtongZhang-alt/BN | 5f4741254398424b730c9a893220a51e1cd829c5 |
| Original frozen Mathlib dependency of the extracted source | leanprover-community/mathlib4 | 79d0395a1825a6264ad5d269e35e60537518955e |
| Mathlib dependency of this port | leanprover-community/mathlib4 | c55e6e786f49471c72fbddbec5415808896aec1e |

`Transfer`, `LocalCliques`, `ScalarCertificate`, and `Concrete` are copied from
the existing local edge-local formalization and adapted only for the current
module system and dependency environment. The original tree is preserved.
Evidence outside this package records source hashes, exact commands, and audits.
