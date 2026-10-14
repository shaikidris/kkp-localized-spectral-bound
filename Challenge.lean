module
public import Mathlib
public import Mathlib.Analysis.Matrix.Spectrum
@[expose] public section

/-!
# The localized two-eigenvalue bound

For a finite noncomplete simple graph with at least two vertices, the squares
of its two largest ordered adjacency eigenvalues sum to at most
`∑_{e∈E(G)} 2(1−1/c(e))`, where `c(e)` is the largest clique containing the edge.
The linear order selects one orientation of each unordered edge.
-/

namespace BN
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Adjacency eigenvalues, with algebraic multiplicity. -/
noncomputable def adjacencyEigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues
/-- Adjacency eigenvalues in nonincreasing order. -/
noncomputable def adjacencyEigenvalues₀ (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin (Fintype.card V) → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues₀
/-- The largest adjacency eigenvalue. -/
noncomputable def lambda1 (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩
/-- The second largest adjacency eigenvalue; it is not replaced by its absolute value. -/
noncomputable def lambda2 (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
end BN

namespace LocalBN
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The maximum cardinality of a clique containing both endpoints. -/
noncomputable def edgeCliqueNum (G : SimpleGraph V) (i j : V) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : Finset V => G.IsClique (s : Set V) ∧
    i ∈ s ∧ j ∈ s).sup Finset.card
/-- Each unordered edge contributes `1−1/c(e)` once. -/
noncomputable def edgeCliqueBudget [LinearOrder V] (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then 1-1/(edgeCliqueNum G i j : ℝ) else 0
/-- KKP Conjecture 1.15 for finite noncomplete simple graphs. Connectedness is unnecessary.
The complete-graph exclusion ensures that the second ordered eigenvalue is nonnegative. -/
theorem edgeLocalizedNoncompleteUnordered [Nontrivial V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G ≠ ⊤) :
    BN.lambda1 G ^ 2 + BN.lambda2 G ^ 2 ≤ 2 * edgeCliqueBudget G := by
  sorry
end LocalBN
