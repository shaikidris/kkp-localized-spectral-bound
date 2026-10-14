/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Authors: Shengtong Zhang (upstream).
Local modifications and adapters produced with Codex; upstream source unmodified.
-/
/-
Local edge-clique certificate; Codex-assisted exploratory source.
The support compression follows Bradač (2022) and adapts BN/MS/Basic.lean
by Shengtong Zhang (Apache-2.0); upstream source and notices are retained.
-/
module
public import Transfer
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order.Compact
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix BN
namespace LocalBN
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

/-- Maximum cardinality of a clique containing both endpoints; zero if none. -/
def edgeCliqueNum (G : SimpleGraph V) (i j : V) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : Finset V => G.IsClique (s : Set V) ∧ i ∈ s ∧ j ∈ s).sup Finset.card

lemma card_le_edgeCliqueNum (G : SimpleGraph V) {s : Finset V}
    (hc : G.IsClique (s : Set V)) {i j : V} (hi : i ∈ s) (hj : j ∈ s) :
    s.card ≤ edgeCliqueNum G i j := by
  classical
  exact Finset.le_sup (f := Finset.card) (by simp [hc, hi, hj])

lemma two_le_edgeCliqueNum (G : SimpleGraph V) {i j : V} (hij : G.Adj i j) :
    2 ≤ edgeCliqueNum G i j := by
  have hc : G.IsClique (↑({i,j} : Finset V) : Set V) :=
    by simpa using G.isClique_pair.mpr (fun _ => hij)
  have hh := card_le_edgeCliqueNum G hc (by simp : i ∈ ({i,j} : Finset V))
    (by simp : j ∈ ({i,j} : Finset V))
  simpa [hij.ne] using hh

lemma edgeCliqueNum_symm (G : SimpleGraph V) (i j : V) :
    edgeCliqueNum G i j = edgeCliqueNum G j i := by
  classical
  simp only [edgeCliqueNum, and_comm, and_assoc]

/-- The reciprocal edge-local coefficient, zero off edges. -/
def edgeWeight (G : SimpleGraph V) : Matrix V V ℝ := by
  classical
  exact fun i j => if G.Adj i j then (edgeCliqueNum G i j : ℝ) /
    ((edgeCliqueNum G i j : ℝ) - 1) else 0

lemma edgeWeight_diag (G : SimpleGraph V) (i : V) : edgeWeight G i i = 0 := by
  classical
  simp [edgeWeight]

lemma edgeWeight_nonedge (G : SimpleGraph V) {i j : V} (hij : ¬G.Adj i j) :
    edgeWeight G i j = 0 := by
  classical
  simp [edgeWeight, hij]

lemma edgeWeight_symm (G : SimpleGraph V) : (edgeWeight G).IsSymm := by
  classical
  ext i j
  simp only [transpose_apply, edgeWeight, G.adj_comm, edgeCliqueNum_symm G j i]

lemma edgeWeight_nonneg (G : SimpleGraph V) (i j : V) : 0 ≤ edgeWeight G i j := by
  classical
  by_cases ha : G.Adj i j
  · have hc : (2 : ℝ) ≤ edgeCliqueNum G i j := by exact_mod_cast two_le_edgeCliqueNum G ha
    simp only [edgeWeight, if_pos ha]
    exact div_nonneg (by linarith) (by linarith)
  · simp [edgeWeight, ha]

/-- Affinity of any supported symmetric zero-diagonal quadratic along a nonedge. -/
lemma weightedQuadratic_transfer {W : Matrix V V ℝ} (hW : W.IsSymm)
    (hdiag : ∀ i, W i i = 0) {i j : V} (_hne : i ≠ j)
    (hij : W i j = 0) (y : V → ℝ) (t : ℝ) :
    (y + t • (BN.e i - BN.e j)) ⬝ᵥ W *ᵥ (y + t • (BN.e i - BN.e j)) =
      y ⬝ᵥ W *ᵥ y + 2*t*((W *ᵥ y) i - (W *ᵥ y) j) := by
  let d := BN.e i - BN.e j
  have hji : W j i = 0 := by rw [hW.apply i j]; exact hij
  have hsingle (k : V) (x : V → ℝ) : BN.e k ⬝ᵥ x = x k := by
    simp [BN.e]
  have hcol (k l : V) : (W *ᵥ BN.e l) k = W k l := by simp [BN.e]
  have hd : d ⬝ᵥ W *ᵥ d = 0 := by
    simp only [d, mulVec_sub, sub_dotProduct, dotProduct_sub, hsingle, hcol]
    simp [hdiag, hij, hji]
  have hsym : y ⬝ᵥ W *ᵥ d = d ⬝ᵥ W *ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW]
    exact dotProduct_comm _ _
  have hdy : d ⬝ᵥ W *ᵥ y = (W *ᵥ y) i - (W *ᵥ y) j := by
    simp only [d, sub_dotProduct, hsingle]
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hsym, hd, hdy]
  ring

/-- On an edge, the maximum is attained by an actual containing clique. -/
lemma edgeCliqueNum_attained (G : SimpleGraph V) {i j : V} (ha : G.Adj i j) :
    ∃ s : Finset V, G.IsClique (s : Set V) ∧ i ∈ s ∧ j ∈ s ∧ s.card = edgeCliqueNum G i j := by
  classical
  let t := Finset.univ.filter fun s : Finset V => G.IsClique (s : Set V) ∧ i ∈ s ∧ j ∈ s
  have hc : G.IsClique (↑({i,j} : Finset V) : Set V) :=
    by simpa using G.isClique_pair.mpr (fun _ => ha)
  have ht : t.Nonempty := ⟨{i,j}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, by simp, by simp⟩⟩
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup t ht Finset.card
  have hh : G.IsClique (s : Set V) ∧ i ∈ s ∧ j ∈ s := by simpa [t] using hs
  exact ⟨s, hh.1, hh.2.1, hh.2.2, heq.symm⟩

end
end LocalBN
