import CvS1

/-!
# CvS2a -- a source seen only through the LEVEL-0 coordinates of `𝔅` drops out of (3.128) and of (3.156)
(lane cover_strong_20261016)

Abstract part (any `BaseDataS`, any predicate `Z` on the constraint space):
* `Q_H_apply`: if `Q G Q*` is a unit then `Q (H z) = z` (`H = G Q*(QGQ*)⁻¹`, (3.126)); `H_zero_of_not_unit`: otherwise `H = 0`
  (the encoding's `Ring.inverse`).  Same for `H₁` with `N = Q G₁ Q*`.
* `H_pair_zero`, `H1_pair_zero`: if `⟪x, J⟫ = 0` whenever `Z (Q x)`, then `⟪H z, J⟫ = 0` and `⟪H₁ z, J⟫ = 0` for every `z` with `Z z`
  (in BOTH branches: unit or junk).
* `G1inv_eq_Ginv_of`: if moreover `Z (C₂ A)` for every `A`, the `Δ^{(2)}` term of (3.128) vanishes and `G₁⁻¹ = G⁻¹` (3.122).

Concrete part (the genuine family): the level-`0` coordinates of `𝔅` (`Lvl0Zero`):
* `data_Q_lvl0`: at a level-0 index `(0, b)`, `(Q x)(0, b) = x b` (`Q_0 = id`, `QlinB_zero`);
* `data_C2_lvl0`: `C^{(2)}(A)(0, b) = 0` (`C2CompL_zero`);
* `tau_adj_lvl0`: for `k ≥ 1`, `τ* w` has zero level-0 coordinates (`τ` reads level `k` only).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverStrong

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-! ## 1. abstract -/

theorem apply_inverse_of_unit {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {M : X →L[ℝ] X} (hM : IsUnit M) (z : X) : M (Ring.inverse M z) = z := by
  obtain ⟨u, rfl⟩ := hM
  rw [Ring.inverse_unit]
  exact ContinuousLinearMap.ext_iff.mp u.mul_inv z

section Abstract

variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (D : BaseDataS E S F)

theorem Q_H_apply (hM : IsUnit ((D.Q.comp D.G).comp D.Qs)) (z : F) : D.Q (D.H z) = z := by
  unfold BaseDataS.H
  exact apply_inverse_of_unit hM z

theorem H_zero_of_not_unit (hM : ¬ IsUnit ((D.Q.comp D.G).comp D.Qs)) : D.H = 0 := by
  unfold BaseDataS.H
  rw [Ring.inverse_non_unit _ hM]
  simp

theorem Q_H1_apply (T : E →L[ℝ] E) (hM : IsUnit ((D.Q.comp (D.G1 T)).comp D.Qs)) (z : F) : D.Q (D.H1 T z) = z := by
  unfold BaseDataS.H1
  exact apply_inverse_of_unit hM z

theorem H1_zero_of_not_unit (T : E →L[ℝ] E) (hM : ¬ IsUnit ((D.Q.comp (D.G1 T)).comp D.Qs)) : D.H1 T = 0 := by
  unfold BaseDataS.H1
  rw [Ring.inverse_non_unit _ hM]
  simp

theorem H_pair_zero (Z : F → Prop) (hJ : ∀ x, Z (D.Q x) → ⟪x, D.J⟫ = 0) {z : F} (hz : Z z) :
    ⟪D.H z, D.J⟫ = 0 := by
  by_cases hM : IsUnit ((D.Q.comp D.G).comp D.Qs)
  · exact hJ _ (by rw [Q_H_apply D hM]; exact hz)
  · rw [H_zero_of_not_unit D hM]
    simp

theorem H1_pair_zero (Z : F → Prop) (hJ : ∀ x, Z (D.Q x) → ⟪x, D.J⟫ = 0) (T : E →L[ℝ] E) {z : F} (hz : Z z) :
    ⟪D.H1 T z, D.J⟫ = 0 := by
  by_cases hM : IsUnit ((D.Q.comp (D.G1 T)).comp D.Qs)
  · exact hJ _ (by rw [Q_H1_apply D T hM]; exact hz)
  · rw [H1_zero_of_not_unit D T hM]
    simp

/-- the `Δ^{(2)}` term of (3.128) vanishes, so `G₁⁻¹ = G⁻¹`. -/
theorem G1inv_eq_Ginv_of (hL : D.Laws) (Z : F → Prop) (hJ : ∀ x, Z (D.Q x) → ⟪x, D.J⟫ = 0)
    (hC : ∀ A, Z (D.C2 A)) {T : E →L[ℝ] E} (hT : D.IsG1inv T) : T = D.Ginv :=
  D.G1inv_unique hT ⟨fun x y => D.Ginv_symm hL x y, fun A => by
    rw [D.K_eq, H_pair_zero D Z hJ (hC A)]
    ring⟩

end Abstract

/-! ## 2. the level-0 coordinates of `𝔅` -/

/-- `z ∈ L²(𝔅)` has zero level-`0` coordinates. -/
def Lvl0Zero {L : PeriodicLatticeExtent} (G : TowerGeom L) (z : FSp G) : Prop :=
  ∀ p : BIdx G, (p.1 : ℕ) = 0 → (WithLp.ofLp z) p = 0

theorem data_Q_lvl0 (P : IngrBParams) (x : ↥(bondSupp P.G)) (p : BIdx P.G) (hp : (p.1 : ℕ) = 0) :
    (WithLp.ofLp (P.data.Q x)) p = (WithLp.ofLp (iE P.G x)) p.2.1 := by
  show (WithLp.ofLp (QfullOf P.G P.U (iE P.G x))) p = _
  simp only [QfullOf, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  have key : ∀ (j : ℕ), j = 0 → ∀ b : Bond (scaleUp P.ell P.k P.Lu),
      (((P.G.ell : ℝ) ^ j)⁻¹) • (WithLp.ofLp (QlinB P.G P.U j (iE P.G x))) b = (WithLp.ofLp (iE P.G x)) b := by
    rintro j rfl b
    rw [pow_zero, inv_one, one_smul, QlinB_zero]
  exact key _ hp _

theorem data_C2_lvl0 (P : IngrBParams) (A : ↥(bondSupp P.G)) : Lvl0Zero P.G (P.data.C2 A) := by
  intro p hp
  show (WithLp.ofLp (C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G A)))) p = 0
  simp only [C2fullOf, WithLp.ofLp_toLp]
  have key : ∀ (j : ℕ), j = 0 → ∀ (X : BondFnL2 (scaleUp P.ell P.k P.Lu)) (b : Bond (scaleUp P.ell P.k P.Lu)),
      (((P.G.ell : ℝ) ^ j)⁻¹) • (WithLp.ofLp (C2rawB P.G P.U j X)) b = 0 := by
    rintro j rfl X b
    rw [C2rawB_eq, C2CompL_zero, map_zero]
    simp
  exact key _ hp _ _

/-- `τ` (top-level extraction) kills every field supported off level `k`. -/
theorem tau_single_zero (P : IngrBParams) (hk : 1 ≤ P.k) (p : BIdx P.G) (hp : (p.1 : ℕ) = 0) (X : SuTwo) :
    P.tau (WithLp.toLp 2 (Pi.single p X)) = 0 := by
  refine PiLp.ext (fun e => ?_)
  show (WithLp.ofLp (tauExt P.ell P.k P.Lu P.hell P.S (WithLp.toLp 2 (Pi.single p X)))) e = 0
  simp only [tauExt, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  split_ifs with hb
  · rw [Pi.single_apply, if_neg]
    intro h
    have h1 := congrArg (fun q : BIdx P.G => (q.1 : ℕ)) h
    simp only [Fin.val_last] at h1
    omega
  · rfl

theorem tau_adj_lvl0 (P : IngrBParams) (hk : 1 ≤ P.k) (w : BondFnL2 P.Lu) :
    Lvl0Zero P.G (ContinuousLinearMap.adjoint P.tau w) := by
  intro p hp
  set f := ContinuousLinearMap.adjoint P.tau w with hf
  have key : ∀ X : SuTwo, ⟪(WithLp.ofLp f) p, X⟫ = 0 := by
    intro X
    have h1 : ⟪f, WithLp.toLp 2 (Pi.single p X)⟫ = ⟪(WithLp.ofLp f) p, X⟫ := by
      rw [PiLp.inner_apply]
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Pi.single_apply, hq]
      · intro h; exact absurd (Finset.mem_univ p) h
    rw [← h1, hf, ContinuousLinearMap.adjoint_inner_left, tau_single_zero P hk p hp X, inner_zero_right]
  have := key ((WithLp.ofLp f) p)
  exact inner_self_eq_zero.mp this

#print axioms apply_inverse_of_unit
#print axioms Q_H_apply
#print axioms H_zero_of_not_unit
#print axioms Q_H1_apply
#print axioms H1_zero_of_not_unit
#print axioms H_pair_zero
#print axioms H1_pair_zero
#print axioms G1inv_eq_Ginv_of
#print axioms data_Q_lvl0
#print axioms data_C2_lvl0
#print axioms tau_single_zero
#print axioms tau_adj_lvl0

end AdalyFormal.CoverStrong
