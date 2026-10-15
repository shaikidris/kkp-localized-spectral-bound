# The localized two-eigenvalue bound

For every finite noncomplete simple graph with at least two vertices,

\[
\lambda_1(G)^2+\lambda_2(G)^2
\le \sum_{e\in E(G)}2\left(1-\frac1{c(e)}\right),
\]

where the adjacency eigenvalues are ordered decreasingly and `c(e)` is the maximum
size of a clique containing `e`. Connectedness is unnecessary. This is the literal
statement of Kannan–Kumar–Pragada Conjecture 1.15.

The proof first establishes the edge-clique scalar certificate by support compression,
then applies the completely positive spectral lift from the BN development. The
localized conclusion does not use the global weighted BN inequality as a theorem.
The noncomplete-graph comparison supplies nonnegativity of the second eigenvalue.

`Challenge.lean` imports only Mathlib and exposes every definition in the selected
statement. `Solution.lean` exports `LocalBN.edgeLocalizedNoncompleteUnordered` from
`Concrete.lean`. `SubmissionAudit.lean` audits its axioms and local dependency chain.

This compatibility candidate uses Lean 4.35.0-rc3 and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. The theorem uses `propext`,
`Classical.choice`, and `Quot.sound`. The supported bundled Comparator requires Linux.
Commit-specific build, preparation, and independent-kernel verdicts are available
in the GitHub Actions artifacts; a green wrapper alone is not proof evidence.
The public source repository is
<https://github.com/shaikidris/kkp-localized-spectral-bound>.
Its GitHub rehearsal runs the pinned Palomar preparation entry point and a
sandboxed Linux Comparator with NanoDa and con-ron. This rehearsal is distinct
from the full Palomar workflow, rendering, editorial review, and registration.

Commands from this directory:

```sh
lake build Challenge Solution SubmissionAudit
lake comparator --config comparator.json
```

BN source and licence notices are retained. The local adapters are drawn from the
existing edge-local project and ported into this isolated directory. See
`SOURCE_PROVENANCE.md` for the roles of the exact source and dependency revisions.

The compatibility branch preserves the theorem and every Lean source file from
`3d74cb4ed4dc2ec2a30fc24f020fe040030a7954`. It resolves the complete Mathlib dependency
closure to agree with the release-selected Verso renderer. The release rehearsal
first checks the pinned request/metadata contract and renderer manifest merge,
then regenerates this project's lockfile with Lake, and requires both the complete
pinned mechanical replay and the exact Challenge render report to pass. These
are separate gates; the earlier mechanical success does not establish rendering
success for this candidate. Registration remains a separate user decision.
