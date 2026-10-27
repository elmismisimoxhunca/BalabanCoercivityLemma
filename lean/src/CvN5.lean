import CvN4

/-!
# CvN5 -- the two endpoints of the path (lane cover_necessary_20261016)

* `Ginv_form`: `⟪x, Ginv x⟫ = ⟪W x, Δ W x⟫ + ‖T x‖² + ⟪x, Q*aQ x⟫` on `E₀` (3.122).
* `Ginv_psd_one` (θ = 0): at the constant configuration `U ≡ 1` the operator `Ginv` is positive semidefinite
  (`Δ(1) = D*χD`: the `Δ'` terms vanish because `Re U(∂p) - 1 = 0` and `Im U(∂p) = 0`).
* `Ginv_neg_flip` (θ = π): at `U = 1[b ↦ -1]`, with `b` based farther than `9 ell` from `Ω₁`, `b` a bond of `E₀`, and a plaquette
  `p₀ ∈ plaqIn Ω₀` having `b` as a boundary bond, the single-bond field `y = X δ_b` has
  `⟪y, Ginv y⟫ ≤ (a - 1) ‖X‖²`: `R D* y = 0` (so `T y = 0`, `W y = y`), the mass term is at most `a ‖X‖²`, and every plaquette
  contributes `cos π ‖X‖² = -‖X‖²` if it contains `b`, `0` otherwise.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply gradValueCovariant curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (inner_eq_trace)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}


/-! ## 0. the form of `Ginv` -/

theorem Ginv_form (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, P.data.Ginv x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x), Delta P.G P.U (Wop P.G P.U P.a (iE P.G x))⟫ +
        ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 + ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
  rw [BaseDataS.inner_Ginv]
  have e1 : ⟪x, P.data.Dpi x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x), Delta P.G P.U (Wop P.G P.U P.a (iE P.G x))⟫ := by
    show ⟪x, ((pE P.G).comp ((DpiFull P.G P.U P.a).comp (iE P.G))) x⟫ = _
    rw [ContinuousLinearMap.comp_apply, pE_inner_right]
    unfold DpiFull
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have e2 : P.data.T x = Tfull P.G P.U (iE P.G x) := rfl
  have e3 : ⟪x, P.data.Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
    show ⟪x, ((pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G))) x⟫ = _
    rw [ContinuousLinearMap.comp_apply, pE_inner_right]
    rfl
  rw [e1, e2, e3]

theorem mass_nonneg (G : TowerGeom L) {a : ℝ} (ha : 0 ≤ a) (S : BondSector G) (A : BondFnL2 L) :
    0 ≤ ⟪A, MassFull G a S A⟫ := by
  rw [inner_MassFull]
  exact Finset.sum_nonneg (fun p _ => by positivity)

/-! ## 1. θ = 0 -/

theorem hol_one (p : PeriodicLatticePlaquette L) :
    periodicPlaquetteHolonomy (fun _ : Bond L => (1 : SU2m)) p = 1 := by
  simp [periodicPlaquetteHolonomy]

theorem reHol_one (p : PeriodicLatticePlaquette L) : reHolonomy (fun _ : Bond L => (1 : SU2m)) p = 1 := by
  unfold reHolonomy holonomyElemInv holonomyElem
  rw [hol_one, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

theorem imHol_one (p : PeriodicLatticePlaquette L) : imHolonomy (fun _ : Bond L => (1 : SU2m)) p = 0 := by
  unfold imHolonomy holonomyElemInv holonomyElem
  rw [hol_one, inv_one, sub_self, smul_zero]

theorem bilPlaq_one (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    bilPlaq (fun _ : Bond L => (1 : SU2m)) p A B = 0 := by
  rw [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply]
  simp only [pairBil_apply, reHol_one, imHol_one, sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  norm_num

theorem Delta_one_nonneg (G : TowerGeom L) (y : BondFnL2 L) : 0 ≤ ⟪y, Delta G (fun _ => 1) y⟫ := by
  unfold Delta
  rw [inner_deltaKLocCLM]
  have h0 : deltaPrimeBilL2NormLoc (fun _ : Bond L => (1 : SU2m)) (plaqIn G.Om0) y y = 0 := by
    show deltaPrimeBilNormLoc (fun _ : Bond L => (1 : SU2m)) (plaqIn G.Om0) (WithLp.ofLp y) (WithLp.ofLp y) = 0
    simp [deltaPrimeBilNormLoc, deltaPrimeBilRawLoc_apply, bilPlaq_one]
  rw [h0, add_zero]
  exact real_inner_self_nonneg

theorem Ginv_psd_one (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a) (x : ↥(bondSupp P.G)) :
    0 ≤ ⟪x, P.data.Ginv x⟫ := by
  rw [Ginv_form]
  have h1 : 0 ≤ ⟪Wop P.G P.U P.a (iE P.G x), Delta P.G P.U (Wop P.G P.U P.a (iE P.G x))⟫ := by
    rw [hU]; exact Delta_one_nonneg _ _
  have h2 := mass_nonneg P.G ha P.sector (iE P.G x)
  positivity

/-! ## 2. θ = π: the configuration `1[b ↦ -1]` -/

section flip
variable (b : Bond L)

/-- `1[b ↦ -1]` -/
noncomputable def Upi : Cfg L := Function.update (fun _ => (1 : SU2m)) b AdalyFormal.NoCover.negOne

theorem Upi_coe (e : Bond L) : ((Upi b e : SU2m) : M2m) = if e = b then -1 else 1 := by
  by_cases h : e = b
  · subst h; simp [Upi, AdalyFormal.NoCover.negOne_coe]
  · simp [Upi, h]

theorem RMap_Upi (e : Bond L) (Z : SuTwo) : RMap (Upi b e) Z = Z := by
  apply Subtype.ext
  rw [RMap_coe_apply, Upi_coe]
  split_ifs <;> simp

theorem Upi_star (e : Bond L) : star ((Upi b e : SU2m) : M2m) = ((Upi b e : SU2m) : M2m) := by
  rw [Upi_coe]; split_ifs <;> simp

end flip

/-! ### the bond field `X δ_b` -/

theorem single_norm_sq (b : Bond L) (X : SuTwo) :
    ‖(WithLp.toLp 2 (Pi.single b X : Bond L → SuTwo) : BondFnL2 L)‖ ^ 2 = ‖X‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_eq_single b]
  · simp
  · intro e _ he; simp [Pi.single_apply, he]
  · intro h; exact absurd (Finset.mem_univ b) h

/-! ### the per-plaquette contribution at `1[b ↦ -1]` -/

theorem shift_ne {L : PeriodicLatticeExtent} (hL : ∀ μ, 1 ≤ L μ) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift z μ ≠ z := by
  intro h
  have h1 := congrFun h μ
  simp only [periodicLatticeShift, Function.update_self] at h1
  have h2 : (1 : Fin (L μ + 1)) = 0 := by
    have := congrArg (fun c => c - z μ) h1
    simpa using this
  rw [Fin.one_eq_zero_iff] at h2
  have := hL μ
  omega

theorem trace_flip (C : M2m) :
    (Matrix.trace (Complex.I • C * (Complex.I • C) * ((-1 : M2m) - 1))).re = 2 * (Matrix.trace (C * C)).re := by
  have e : (-1 : M2m) - 1 = (-2 : ℂ) • (1 : M2m) := by
    rw [show (-2 : ℂ) = -1 - 1 by norm_num, sub_smul, neg_smul, one_smul]
  rw [e]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, Matrix.trace_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have : (-2 : ℂ) * (Complex.I * Complex.I) = 2 := by rw [hI]; ring
  rw [this]
  simp [Complex.smul_re]

theorem norm_sq_trace (X : SuTwo) : ‖X‖ ^ 2 = -(1 / 2 : ℝ) * (Matrix.trace ((X : M2m) * (X : M2m))).re := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_trace]

theorem half_neg_two : (1 / 2 : ℂ) • ((-1 : M2m) + -1) = -1 := by
  rw [← two_smul ℂ (-1 : M2m), smul_smul]; norm_num

/-- the curl at `1[b ↦ -1]` is the flat curl (`R(±1) = id`). -/
theorem curl_Upi (b : Bond L) (A : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ ν : Fin 3) (h : μ < ν) :
    curlValueCovariant (Upi b) A ((z, ⟨(μ, ν), h⟩) : PeriodicLatticePlaquette L) =
      A (z, μ) + A (periodicLatticeShift z μ, ν) - A (periodicLatticeShift z ν, μ) - A (z, ν) := by
  simp only [curlValueCovariant, RMap_Upi]

theorem reHol_Upi (b : Bond L) (z : PeriodicLatticeSite L) (μ ν : Fin 3) (h : μ < ν) :
    reHolonomy (Upi b) ((z, ⟨(μ, ν), h⟩) : PeriodicLatticePlaquette L) =
      (1 / 2 : ℂ) • (((Upi b (z, μ) : SU2m) : M2m) * ((Upi b (periodicLatticeShift z μ, ν) : SU2m) : M2m) *
        ((Upi b (periodicLatticeShift z ν, μ) : SU2m) : M2m) * ((Upi b (z, ν) : SU2m) : M2m) +
        ((Upi b (z, ν) : SU2m) : M2m) * ((Upi b (periodicLatticeShift z ν, μ) : SU2m) : M2m) *
        ((Upi b (periodicLatticeShift z μ, ν) : SU2m) : M2m) * ((Upi b (z, μ) : SU2m) : M2m)) := by
  unfold reHolonomy holonomyElemInv holonomyElem periodicPlaquetteHolonomy
  simp only [su_coe_mul, su_coe_inv, star_mul, star_star, Upi_star, Matrix.mul_assoc]

theorem imHol_Upi (b : Bond L) (p : PeriodicLatticePlaquette L) : imHolonomy (Upi b) p = 0 := by
  unfold imHolonomy holonomyElemInv holonomyElem periodicPlaquetteHolonomy
  simp only [su_coe_mul, su_coe_inv, star_mul, star_star, Upi_star, Upi_coe]
  split_ifs <;> simp

theorem second_Upi (b : Bond L) (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    secondBilPlaq (Upi b) p A B = 0 := by
  rw [secondBilPlaq_apply]
  simp only [pairBil_apply, imHol_Upi, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, sub_zero, add_zero]

#print axioms Ginv_form
#print axioms mass_nonneg
#print axioms hol_one
#print axioms reHol_one
#print axioms imHol_one
#print axioms bilPlaq_one
#print axioms Delta_one_nonneg
#print axioms Ginv_psd_one
#print axioms Upi
#print axioms Upi_coe
#print axioms RMap_Upi
#print axioms Upi_star
#print axioms single_norm_sq
#print axioms shift_ne
#print axioms trace_flip
#print axioms norm_sq_trace
#print axioms half_neg_two
#print axioms curl_Upi
#print axioms reHol_Upi
#print axioms imHol_Upi
#print axioms second_Upi

end AdalyFormal.CoverNec
