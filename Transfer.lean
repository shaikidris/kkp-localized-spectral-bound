/-
Local exploratory transfer, generated with Codex on 2026-10-13.
Imports the Apache-2.0 BN development by Shengtong Zhang and collaborators.
Upstream source is unmodified; see ../upstream/LICENSE and the upstream metadata ../upstream/formalization.yaml.
-/
module
public import BN.Spectral.Weighted
@[expose] public section

/-! A general scalar-certificate transfer. The certificate is an explicit premise;
this module does not yet formalize Bradač's edge-clique producer. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix BN
open scoped Matrix
namespace LocalBN

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Factorwise passage of a homogeneous scalar certificate to CP matrices. -/
theorem cpPairing {W C : Matrix n n ℝ}
    (hscalar : ∀ y : n → ℝ, (∀ i, 0 ≤ y i) →
      BN.inner W (vecMulVec y y) ≤ (∑ i, y i) ^ 2)
    (hC : IsCompletelyPositive C) :
    BN.inner W C ≤ BN.inner (of fun _ _ => (1 : ℝ)) C := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  rw [BN.inner_sum Finset.univ W (fun a => vecMulVec (p a) (p a))]
  rw [BN.inner_sum Finset.univ (of fun _ _ => (1 : ℝ))
    (fun a => vecMulVec (p a) (p a))]
  simp_rw [BN.inner_one_vecMulVec]
  exact Finset.sum_le_sum fun a _ => hscalar (p a) (hp a)

/-- Reciprocal-weight Cauchy--Schwarz, including zero weights on unused entries. -/
theorem weightedCauchy {α : Type*} [Fintype α]
    (w b p : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsupp : ∀ i, w i = 0 → b i = 0) :
    (∑ i, b i * p i) ^ 2 ≤ (∑ i, b i ^ 2 / w i) * ∑ i, w i * p i ^ 2 := by
  let u := fun i => b i / Real.sqrt (w i)
  let v := fun i => Real.sqrt (w i) * p i
  have huv (i : α) : u i * v i = b i * p i := by
    by_cases hz : w i = 0
    · simp [u, v, hz, hsupp i hz]
    · have hs : Real.sqrt (w i) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (hw i) (Ne.symm hz)))
      dsimp [u, v]
      field_simp
  have hu (i : α) : u i ^ 2 = b i ^ 2 / w i := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt (hw i)]
  have hv (i : α) : v i ^ 2 = w i * p i ^ 2 := by
    dsimp [v]
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ u v
  simpa only [huv, hu, hv] using hcs

/-- Transfer of a scalar certificate through the pinned BN half-plane CP lift.
The conclusion uses ordered pairs. The index type has at least two elements. -/
theorem spectralTransfer [Nontrivial n] {B W : Matrix n n ℝ}
    (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hW : ∀ i j, 0 ≤ W i j) (hWdiag : ∀ i, W i i = 0)
    (hsupp : ∀ i j, W i j = 0 → B i j = 0)
    (hscalar : ∀ y : n → ℝ, (∀ i, 0 ≤ y i) →
      BN.inner W (vecMulVec y y) ≤ (∑ i, y i) ^ 2) :
    F hB ≤ ∑ i, ∑ j, B i j ^ 2 / W i j := by
  classical
  let s := spectralSlice hB hnn
  letI : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  let T : ℝ := ∑ i, ∑ j, W i j * (BN.posPart s.X i j) ^ 2
  let Q : ℝ := ∑ i, ∑ j, B i j ^ 2 / W i j
  have hT : T ≤ F hB := by
    have hpair := cpPairing hscalar s.isCompletelyPositive_M
    have hm : BN.inner W (M s.X) = T := by
      rw [BN.inner_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp [hWdiag]
      · rw [M_apply_of_ne s.X (isHermitian_iff_isSymm.mp s.posSemidef.isHermitian) hij]
    rw [hm] at hpair
    simpa only [show (of fun _ _ => (1 : ℝ)) = BN.ones from rfl,
      inner_ones_M, s.inner_X_X] using hpair
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hW i j)
  have hL : F hB ≤ ∑ i, ∑ j, B i j * BN.posPart s.X i j := by
    rw [← s.inner_B_X, BN.inner_eq_sum]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (le_max_left _ _) (hnn i j)
  have hLnn : 0 ≤ ∑ i, ∑ j, B i j * BN.posPart s.X i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hnn i j) (BN.posPart_nonneg _ _ _)
  have hcs : (∑ i, ∑ j, B i j * BN.posPart s.X i j) ^ 2 ≤ Q * T := by
    have hc := weightedCauchy (fun p : n × n => W p.1 p.2)
      (fun p : n × n => B p.1 p.2) (fun p : n × n => BN.posPart s.X p.1 p.2)
      (fun p => hW p.1 p.2) (fun p => hsupp p.1 p.2)
    simpa only [Fintype.sum_prod_type] using hc
  by_cases hB0 : B = 0
  · have hz : F hB = 0 := by
      rw [← s.inner_B_X, BN.inner_eq_sum]
      simp [hB0]
    rw [hz]
    exact hQ
  · have hFpos : 0 < F hB := by
      rw [← s.inner_X_X]
      exact s.inner_pos hB0
    have hsq : F hB ^ 2 ≤ Q * F hB :=
      (pow_le_pow_left₀ hFpos.le hL 2).trans (hcs.trans (mul_le_mul_of_nonneg_left hT hQ))
    have hrearr : F hB * F hB ≤ Q * F hB := by simpa only [pow_two] using hsq
    exact (mul_le_mul_iff_of_pos_right hFpos).mp hrearr

/-- The same transfer for all finite index types; the small-cardinality case is zero. -/
theorem spectralTransferAll {B W : Matrix n n ℝ}
    (hB : B.IsHermitian) (hnn : ∀ i j, 0 ≤ B i j)
    (hW : ∀ i j, 0 ≤ W i j) (hWdiag : ∀ i, W i i = 0)
    (hsupp : ∀ i j, W i j = 0 → B i j = 0)
    (hscalar : ∀ y : n → ℝ, (∀ i, 0 ≤ y i) →
      BN.inner W (vecMulVec y y) ≤ (∑ i, y i) ^ 2) :
    F hB ≤ ∑ i, ∑ j, B i j ^ 2 / W i j := by
  classical
  cases subsingleton_or_nontrivial n with
  | inl hsmall =>
    letI := hsmall
    have hzero : B = 0 := by
      ext i j
      have hij : i = j := Subsingleton.elim i j
      subst j
      exact hsupp i i (hWdiag i)
    subst B
    simpa only [F_zero, Matrix.zero_apply, zero_pow (by decide : 2 ≠ 0),
      zero_div, Finset.sum_const_zero] using (le_refl (0 : ℝ))
  | inr hlarge =>
    letI := hlarge
    exact spectralTransfer hB hnn hW hWdiag hsupp hscalar

#print axioms LocalBN.cpPairing
#print axioms LocalBN.weightedCauchy
#print axioms LocalBN.spectralTransfer
#print axioms LocalBN.spectralTransferAll
end LocalBN
