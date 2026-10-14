# Source provenance

This package contains substantive proof source. Its authoritative submission
snapshot will be the clean, reviewed commit supplied to the intake; no submission
commit has been created. The exact source roles are:

| Role | Repository | Commit |
|---|---|---|
| Extracted BN proof source | ShengtongZhang-alt/BN | 5f4741254398424b730c9a893220a51e1cd829c5 |
| Original frozen Mathlib dependency of the extracted source | leanprover-community/mathlib4 | 79d0395a1825a6264ad5d269e35e60537518955e |
| Mathlib dependency of this port | leanprover-community/mathlib4 | dd56d02cb7a58fa066c4a2c7fddec3cbb59ae8df |

`Transfer`, `LocalCliques`, `ScalarCertificate`, and `Concrete` are copied from
the existing local edge-local formalization and adapted only for the current
module system and dependency environment. The original tree is preserved.
Evidence outside this package records source hashes, exact commands, and audits.
