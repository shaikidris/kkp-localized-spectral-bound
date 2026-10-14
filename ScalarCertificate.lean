/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in upstream LICENSE.
Authors: Shengtong Zhang (upstream).
Local modifications and adapters produced with Codex; upstream source unmodified.
-/
/-
Weighted support compression, adapting BN/MS/Basic.lean (Shengtong Zhang,
Apache-2.0) to Bradač's edge-local scalar certificate. Codex-assisted additions.
-/
module
public import LocalCliques
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix BN
namespace LocalBN
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

/-- A weighted zero-diagonal graph quadratic has a simplex maximizer on a clique. -/
lemma exists_weighted_maximizer_clique [Nonempty V] (G : SimpleGraph V)
    (W : Matrix V V ℝ) (hW : W.IsSymm) (hdiag : ∀ i, W i i = 0)
    (hsupp : ∀ i j, ¬G.Adj i j → W i j = 0) :
    ∃ y, y ∈ stdSimplex ℝ V ∧
      IsMaxOn (fun y : V → ℝ => y ⬝ᵥ W *ᵥ y) (stdSimplex ℝ V) y ∧
      G.IsClique {v | y v ≠ 0} := by
  classical
  set f : (V → ℝ) → ℝ := fun y => y ⬝ᵥ W *ᵥ y
  have hcont : Continuous f := continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨y0, hy0, hmax0⟩ := (isCompact_stdSimplex ℝ V).exists_isMaxOn
    BN.stdSimplex_nonempty hcont.continuousOn
  have hind : ∀ n : ℕ, ∀ y : V → ℝ, y ∈ stdSimplex ℝ V → IsMaxOn f (stdSimplex ℝ V) y →
      (Finset.univ.filter (fun v => y v ≠ 0)).card = n →
      ∃ z, z ∈ stdSimplex ℝ V ∧ IsMaxOn f (stdSimplex ℝ V) z ∧
        G.IsClique {v | z v ≠ 0} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hy hmax hn
      by_cases hc : G.IsClique {v | y v ≠ 0}
      · exact ⟨y, hy, hmax, hc⟩
      · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne₀, hnad⟩ :=
          (_root_.SimpleGraph.not_isClique_iff (G := G) (s := {v | y v ≠ 0})).mp hc
        have hi : y i ≠ 0 := hi
        have hj : y j ≠ 0 := hj
        have hne : i ≠ j := Subtype.coe_ne_coe.mpr hne₀
        have hyi : 0 < y i := lt_of_le_of_ne (hy.1 i) hi.symm
        have hyj : 0 < y j := lt_of_le_of_ne (hy.1 j) hj.symm
        set δ := (W *ᵥ y) i - (W *ᵥ y) j
        set t := if 0 ≤ δ then y j else -y i
        have hti : 0 ≤ y i + t := by
          by_cases hδ : 0 ≤ δ
          · simp [t, hδ]
            exact add_nonneg (hy.1 i) (hy.1 j)
          · simp [t, hδ]
        have htj : 0 ≤ y j - t := by
          by_cases hδ : 0 ≤ δ
          · simp [t, hδ]
          · simp [t, hδ]
            exact add_nonneg (hy.1 j) (hy.1 i)
        have ht_mul : 0 ≤ t * δ := by
          by_cases hδ : 0 ≤ δ
          · rw [show t = y j from if_pos hδ]
            exact mul_nonneg hyj.le hδ
          · rw [show t = -y i from if_neg hδ]
            exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hyi.le) (le_of_not_ge hδ)
        have ht_ne : t ≠ 0 := by
          by_cases hδ : 0 ≤ δ
          · rw [show t = y j from if_pos hδ]
            exact hyj.ne'
          · rw [show t = -y i from if_neg hδ]
            exact neg_ne_zero.2 hyi.ne'
        have hy' : y + t • (e i - e j) ∈ stdSimplex ℝ V :=
          add_smul_e_sub_e_mem_stdSimplex hne hy hti htj
        have hquad :=
          weightedQuadratic_transfer hW hdiag hne (hsupp i j hnad) y t
        have hf' : f (y + t • (e i - e j)) = f y + 2 * t * δ := by
          simpa [f, δ] using hquad
        have hfyle : f (y + t • (e i - e j)) ≤ f y := hmax hy'
        have hinc0 : 2 * t * δ = 0 := by
          have : 0 ≤ 2 * (t * δ) :=
            mul_nonneg (by positivity : (0 : ℝ) ≤ 2) ht_mul
          linarith
        have hδ0 : δ = 0 := by
          have : t * δ = 0 := by nlinarith
          exact (mul_eq_zero.mp this).resolve_left ht_ne
        have htj0 : t = y j := by simp [t, hδ0]
        have hyj' : (y + t • (e i - e j)) j = 0 := by
          rw [add_smul_e_sub_e_apply hne, if_neg hne.symm, if_pos rfl, htj0]
          ring
        have hmax' : IsMaxOn f (stdSimplex ℝ V) (y + t • (e i - e j)) := by
          intro z hz
          have heq : f (y + t • (e i - e j)) = f y := by
            simp [hf', hδ0]
          rw [heq]
          exact hmax hz
        set y' := y + t • (e i - e j)
        set s := Finset.univ.filter (fun v => y v ≠ 0)
        set s' := Finset.univ.filter (fun v => y' v ≠ 0)
        have hsubset : s' ⊆ s := by
          intro v hv
          simp only [s', s, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          by_cases hvi : v = i
          · subst hvi
            exact hi
          · by_cases hvj : v = j
            · subst hvj
              exact (hv hyj').elim
            · have : y' v = y v := by
                simp [y', add_smul_e_sub_e_apply hne, hvi, hvj]
              rwa [this] at hv
        have hjmem : j ∈ s := by simp [s, hj]
        have hjnot : j ∉ s' := by
          simp [s']
          exact hyj'
        have hss : s' ⊂ s :=
          Finset.ssubset_iff_subset_ne.2 ⟨hsubset, fun h => hjnot (h ▸ hjmem)⟩
        have hn' : s'.card < n := by
          rw [← hn]
          exact Finset.card_lt_card hss
        exact ih s'.card hn' y' hy' hmax' rfl
  exact hind _ y0 hy0 hmax0 rfl

omit [DecidableEq V] in
lemma quadratic_double_sum (W : Matrix V V ℝ) (y : V → ℝ) :
    y ⬝ᵥ W *ᵥ y = ∑ i, ∑ j, W i j * y i * y j := by
  rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma edgeWeight_le_clique_ratio (G : SimpleGraph V) {s : Finset V}
    (hc : G.IsClique (s : Set V)) (hk : 2 ≤ s.card) {i j : V}
    (hi : i ∈ s) (hj : j ∈ s) (hij : G.Adj i j) :
    edgeWeight G i j ≤ (s.card : ℝ) / ((s.card : ℝ)-1) := by
  classical
  have hck : (s.card : ℝ) ≤ edgeCliqueNum G i j := by
    exact_mod_cast card_le_edgeCliqueNum G hc hi hj
  have hkreal : (2 : ℝ) ≤ s.card := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (s.card : ℝ)-1 := by linarith
  have hcpos : (0 : ℝ) < (edgeCliqueNum G i j : ℝ)-1 := by linarith
  simp only [edgeWeight, if_pos hij]
  apply (div_le_div_iff₀ hcpos hkpos).mpr
  nlinarith

lemma edge_quadratic_le_one_clique (G : SimpleGraph V) [DecidableRel G.Adj]
    {y : V → ℝ} (hy : y ∈ stdSimplex ℝ V)
    (hc : G.IsClique {v | y v ≠ 0}) : y ⬝ᵥ edgeWeight G *ᵥ y ≤ 1 := by
  classical
  set s := Finset.univ.filter (fun v => y v ≠ 0)
  have hs_set : (s : Set V) = {v | y v ≠ 0} := by ext; simp [s]
  have hs : G.IsClique (s : Set V) := by simpa [hs_set] using hc
  have hsupp : ∀ v, y v ≠ 0 → v ∈ s := by intro v hv; simp [s, hv]
  by_cases hk : 2 ≤ s.card
  · let r : ℝ := (s.card : ℝ) / ((s.card : ℝ)-1)
    have hkreal : (2 : ℝ) ≤ s.card := by exact_mod_cast hk
    have hr : 0 ≤ r := div_nonneg (by linarith) (by linarith)
    have hcompare : y ⬝ᵥ edgeWeight G *ᵥ y ≤ r * (y ⬝ᵥ G.adjMatrix ℝ *ᵥ y) := by
      rw [quadratic_double_sum, quadratic_double_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases ha : G.Adj i j
      · simp only [SimpleGraph.adjMatrix_apply, if_pos ha, one_mul]
        by_cases hi : y i = 0
        · simp [hi]
        by_cases hj : y j = 0
        · simp [hj]
        have hw : edgeWeight G i j ≤ r := edgeWeight_le_clique_ratio G hs hk
          (hsupp i hi) (hsupp j hj) ha
        have hprod : 0 ≤ y i * y j := mul_nonneg (hy.1 i) (hy.1 j)
        nlinarith [mul_le_mul_of_nonneg_right hw hprod]
      · simp [edgeWeight_nonedge G ha, SimpleGraph.adjMatrix_apply, ha]
    have hquad := BN.adjMatrix_quadratic_eq_sum_sq_sub_of_isClique hs hsupp
    have hsum : ∑ i, y i = ∑ i ∈ s, y i :=
      (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
        simp [s] at hi; simp [hi]).symm
    have hsq : ∑ i, y i ^ 2 = ∑ i ∈ s, y i ^ 2 :=
      (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
        simp [s] at hi; simp [hi]).symm
    have hcs := BN.sum_sq_sub_sum_sq_le_finset s y (by omega : 1 ≤ s.card)
    have hy1s : ∑ i ∈ s, y i = 1 := by rw [← hsum, hy.2]
    have hbound : y ⬝ᵥ G.adjMatrix ℝ *ᵥ y ≤ 1 - 1/(s.card : ℝ) := by
      rw [hquad, hsum, hsq]
      simpa only [hy1s, one_pow, mul_one] using hcs
    have hcancel : r * (1 - 1/(s.card : ℝ)) = 1 := by
      dsimp [r]
      have hk0 : (s.card : ℝ) ≠ 0 := by linarith
      have hk1 : (s.card : ℝ)-1 ≠ 0 := by linarith
      field_simp
    exact hcompare.trans ((mul_le_mul_of_nonneg_left hbound hr).trans_eq hcancel)
  · have hsmall : (s : Set V).Subsingleton :=
      Finset.card_le_one_iff_subsingleton.mp (by omega : s.card ≤ 1)
    have hzero : y ⬝ᵥ edgeWeight G *ᵥ y = 0 := by
      rw [quadratic_double_sum]
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      by_cases hi : y i = 0
      · simp [hi]
      by_cases hj : y j = 0
      · simp [hj]
      have hij : i = j := hsmall (hsupp i hi) (hsupp j hj)
      subst j
      simp [edgeWeight_diag]
    rw [hzero]
    norm_num

lemma edge_quadratic_simplex [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {y : V → ℝ} (hy : y ∈ stdSimplex ℝ V) :
    y ⬝ᵥ edgeWeight G *ᵥ y ≤ 1 := by
  obtain ⟨z, hz, hmax, hc⟩ := exists_weighted_maximizer_clique G (edgeWeight G)
    (edgeWeight_symm G) (edgeWeight_diag G) (fun _ _ => edgeWeight_nonedge G)
  exact (hmax hy).trans (edge_quadratic_le_one_clique G hz hc)

/-- Bradač's exact homogeneous edge-local scalar certificate. No supplied premise. -/
theorem edgeCliqueScalar (G : SimpleGraph V) [DecidableRel G.Adj]
    {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) :
    y ⬝ᵥ edgeWeight G *ᵥ y ≤ (∑ i, y i) ^ 2 := by
  classical
  by_cases h0 : ∑ i, y i = 0
  · have hy0 : y = 0 := by
      ext i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hy j)).1 h0 i (Finset.mem_univ i)
    simp [hy0]
  · have hV : Nonempty V := by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
      exact ⟨i⟩
    letI := hV
    set σ := ∑ i, y i
    have hσpos : 0 < σ := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hy i) (Ne.symm h0)
    set z : V → ℝ := σ⁻¹ • y
    have hz : z ∈ stdSimplex ℝ V := by
      refine ⟨fun i => mul_nonneg (inv_nonneg.2 hσpos.le) (hy i), ?_⟩
      change ∑ i, σ⁻¹ * y i = 1
      rw [← Finset.mul_sum, inv_mul_cancel₀ h0]
    have hzle := edge_quadratic_simplex G hz
    have hscale : z ⬝ᵥ edgeWeight G *ᵥ z = σ⁻¹ ^ 2 * (y ⬝ᵥ edgeWeight G *ᵥ y) := by
      simp [z, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two, mul_assoc]
    have heq : y ⬝ᵥ edgeWeight G *ᵥ y = σ^2 * (z ⬝ᵥ edgeWeight G *ᵥ z) := by
      rw [hscale]
      field_simp [h0]
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hzle (sq_nonneg σ)).trans_eq (mul_one _)

#print axioms LocalBN.edgeCliqueScalar
end
end LocalBN
