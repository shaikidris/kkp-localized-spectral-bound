/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Authors: Shengtong Zhang (upstream).
Local modifications and adapters produced with Codex; upstream source unmodified.
-/
/-
Concrete edge-local BN consequence. Codex-assisted local source.
Uses the pinned Apache-2.0 BN CP development and Bradač's scalar proof.
-/
module
public import ScalarCertificate
public import BN.Spectral.Interlace
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix BN
namespace LocalBN
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

/-- Ordered edge sum of the edge-clique coefficient times squared matrix entries. -/
def edgeEnergy (G : SimpleGraph V) (B : Matrix V V ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if G.Adj i j then (1 - 1/(edgeCliqueNum G i j : ℝ))*B i j^2 else 0

lemma edgeWeight_pos (G : SimpleGraph V) {i j : V} (ha : G.Adj i j) :
    0 < edgeWeight G i j := by
  classical
  have hc : (2 : ℝ) ≤ edgeCliqueNum G i j := by exact_mod_cast two_le_edgeCliqueNum G ha
  simp only [edgeWeight, if_pos ha]
  exact div_pos (by linarith) (by linarith)

lemma reciprocal_sum_eq_energy (G : SimpleGraph V) (B : Matrix V V ℝ) :
    (∑ i, ∑ j, B i j^2 / edgeWeight G i j) = edgeEnergy G B := by
  classical
  unfold edgeEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases ha : G.Adj i j
  · have hc : (2 : ℝ) ≤ edgeCliqueNum G i j := by exact_mod_cast two_le_edgeCliqueNum G ha
    have hc0 : (edgeCliqueNum G i j : ℝ) ≠ 0 := by linarith
    have hc1 : (edgeCliqueNum G i j : ℝ)-1 ≠ 0 := by linarith
    simp only [edgeWeight, if_pos ha]
    field_simp
  · simp [edgeWeight, ha]

/-- The concrete weighted edge-local bound, with the scalar producer discharged. -/
theorem edgeLocalizedWeighted (G : SimpleGraph V) {B : Matrix V V ℝ}
    (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hdiag : ∀ i, B i i = 0)
    (hsupp : ∀ i j, ¬G.Adj i j → B i j = 0) :
    F hB ≤ edgeEnergy G B := by
  classical
  have hs : ∀ i j, edgeWeight G i j = 0 → B i j = 0 := by
    intro i j hz
    by_cases hij : i = j
    · subst j
      exact hdiag i
    by_cases ha : G.Adj i j
    · exact (ne_of_gt (edgeWeight_pos G ha) hz).elim
    · exact hsupp i j ha
  have hscalar : ∀ y : V → ℝ, (∀ i, 0 ≤ y i) →
      BN.inner (edgeWeight G) (vecMulVec y y) ≤ (∑ i, y i)^2 := by
    intro y hy
    rw [BN.inner_vecMulVec]
    exact edgeCliqueScalar G hy
  have ht := spectralTransferAll hB hnn (edgeWeight_nonneg G) (edgeWeight_diag G) hs hscalar
  rwa [reciprocal_sum_eq_energy] at ht

/-- Kannan--Kumar--Pragada's noncomplete-graph edge-local conjecture, ordered form. -/
theorem edgeLocalizedNoncomplete [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G ≠ ⊤) :
    BN.lambda1 G ^ 2 + BN.lambda2 G ^ 2 ≤ edgeEnergy G (G.adjMatrix ℝ) := by
  classical
  have ht := edgeLocalizedWeighted G (G.isHermitian_adjMatrix ℝ)
    (fun i j => by simp only [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num)
    (fun i => by simp [SimpleGraph.adjMatrix_apply])
    (fun i j hn => by simp [SimpleGraph.adjMatrix_apply, hn])
  rwa [BN.F_adjMatrix_eq G hG] at ht

/-- Each edge counted once by the chosen linear order. -/
def edgeEnergyUnordered [LinearOrder V] (G : SimpleGraph V) (B : Matrix V V ℝ) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then
    (1 - 1/(edgeCliqueNum G i j : ℝ))*B i j^2 else 0

lemma sum_symmetric_eq_twice_upper [LinearOrder V] (f : V → V → ℝ)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * (∑ i, ∑ j, if i < j then f i j else 0) := by
  have hsplit (i j : V) : f i j = (if i < j then f i j else 0) +
      (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j
      simp [hdiag]
    · simp [h, not_lt_of_ge h.le]
  have hrev : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym j i]
  calc
    (∑ i, ∑ j, f i j) = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      trans ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0))
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
      · simp only [Finset.sum_add_distrib]
    _ = 2 * (∑ i, ∑ j, if i < j then f i j else 0) := by rw [hrev]; ring

lemma edgeEnergy_eq_twice_unordered [LinearOrder V] (G : SimpleGraph V)
    {B : Matrix V V ℝ} (hB : B.IsHermitian) :
    edgeEnergy G B = 2 * edgeEnergyUnordered G B := by
  classical
  let f := fun i j => if G.Adj i j then (1-1/(edgeCliqueNum G i j : ℝ))*B i j^2 else 0
  have hsym : ∀ i j, f i j = f j i := by
    intro i j
    dsimp [f]
    rw [G.adj_comm i j, edgeCliqueNum_symm G i j,
      (isHermitian_iff_isSymm.mp hB).apply j i]
  have hdiag : ∀ i, f i i = 0 := by intro i; simp [f]
  have hh := sum_symmetric_eq_twice_upper f hsym hdiag
  simpa only [edgeEnergy, edgeEnergyUnordered, f, ite_and] using hh

/-- Literal nonnegative weighted bound with unordered edges counted once. -/
theorem edgeLocalizedWeightedUnordered [LinearOrder V] (G : SimpleGraph V)
    {B : Matrix V V ℝ} (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hdiag : ∀ i, B i i = 0) (hsupp : ∀ i j, ¬G.Adj i j → B i j = 0) :
    F hB ≤ 2 * edgeEnergyUnordered G B := by
  have ht := edgeLocalizedWeighted G hB hnn hdiag hsupp
  rwa [edgeEnergy_eq_twice_unordered G hB] at ht

/-- Unordered edge-clique budget for a simple adjacency matrix. -/
def edgeCliqueBudget [LinearOrder V] (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ i, ∑ j, if i < j ∧ G.Adj i j then 1-1/(edgeCliqueNum G i j : ℝ) else 0

/-- The noncomplete-graph conjecture, with the literal unordered edge budget. -/
theorem edgeLocalizedNoncompleteUnordered [Nontrivial V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G ≠ ⊤) :
    BN.lambda1 G^2 + BN.lambda2 G^2 ≤ 2 * edgeCliqueBudget G := by
  classical
  have ht := edgeLocalizedNoncomplete G hG
  rw [edgeEnergy_eq_twice_unordered G (G.isHermitian_adjMatrix ℝ)] at ht
  have heq : edgeEnergyUnordered G (G.adjMatrix ℝ) = edgeCliqueBudget G := by
    unfold edgeEnergyUnordered edgeCliqueBudget
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases ha : G.Adj i j
    · simp [SimpleGraph.adjMatrix_apply, ha]
    · simp [ha]
  rwa [heq] at ht

#print axioms LocalBN.edgeLocalizedWeighted
#print axioms LocalBN.edgeLocalizedNoncomplete
#print axioms LocalBN.edgeLocalizedWeightedUnordered
#print axioms LocalBN.edgeLocalizedNoncompleteUnordered
end
end LocalBN
