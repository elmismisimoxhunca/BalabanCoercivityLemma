import MF7
import DLR2

/-!
# DL3 -- the M0 U-side and the WellDef units with the D-layer premise in FORM shape (copies of MF3 `u_side`, MF5e `units_PU`)

The m0_finish chain consumes the D-layer through `hD2 : ‖Δ⁽²⁾‖ ≤ ε2` only to obtain `|⟪A,Δ⁽²⁾A⟫| ≤ ε2 ‖A‖² ≤ ε2 C0 ⟪A,G⁻¹A⟫`.
Here the premise is the FORM bound `hD2f : |⟪A,Δ⁽²⁾A⟫| ≤ ε' ⟪A,G⁻¹A⟫` directly (DL2 `formD2` produces it without any bound on ‖W‖;
the operator-norm premise would need ‖W‖, W = 1 − DG'RD*, which nothing in the tree bounds).
TEXT COPIES (proof bodies unchanged except the ε2·C0 → ε' bookkeeping): `u_side_f` (MF3 `u_side`), `units_PU_f` (MF5e `units_PU`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG (GenP.genForm GenP.firstTerm GenP.Nmat pe)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M0Finish

/-- **the U side** -/
theorem u_side_f (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (hu : IsUnit (DelpA (PU ell k Lu hell U a Lam).G U a + (1 - siteMask (PU ell k Lu hell U a Lam).G.Om0)))
    (hB0 : ∀ ν ∈ NQp (PU ell k Lu hell U a Lam).G U,
      (bondSectorOf (PU ell k Lu hell U a Lam).G U).Qfull (gradL2 U ν) = 0)
    (hG : IsUnit (PU ell k Lu hell U a Lam).G1inv) (hN : IsUnit (GenP.Nmat (PU ell k Lu hell U a Lam)))
    (C0 ε' εJ : ℝ) (hC0 : 0 < C0) (hε'0 : 0 ≤ ε') (hε'1 : ε' ≤ 1)
    (hcoer : ∀ y : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      ‖y‖ ^ 2 ≤ C0 * ⟪y, (PU ell k Lu hell U a Lam).data.Ginv y⟫)
    (hD2f : ∀ A : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      |⟪A, (PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws A⟫|
        ≤ ε' * ⟪A, (PU ell k Lu hell U a Lam).data.Ginv A⟫)
    (B : BondFnL2 Lu)
    (hJ : |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in B),
        (PU ell k Lu hell U a Lam).Jf⟫| ≤ εJ * ‖B‖ ^ 2) :
    ∃ x : BondFnL2 (scaleUp ell k Lu),
      (bondSectorOf (PU ell k Lu hell U a Lam).G U).Qfull x
          = ContinuousLinearMap.adjoint (PU ell k Lu hell U a Lam).tau B ∧
      ‖x‖ ^ 2 ≤ C0 * (⟪x, Delta (PU ell k Lu hell U a Lam).G U x⟫ + a * (ell : ℝ) ^ k * ‖B‖ ^ 2) ∧
      (1 - ε') * (⟪x, Delta (PU ell k Lu hell U a Lam).G U x⟫ / (ell : ℝ) ^ k)
          - (ε' * a + 2 * εJ) * ‖B‖ ^ 2
        ≤ GenP.genForm (PU ell k Lu hell U a Lam) B := by
  set P := PU ell k Lu hell U a Lam with hP
  have hOm : P.G.Om0 = Set.univ := PU_Om0 ell k Lu hell U a Lam
  have hFS : P.FullSupp := fullTower_fullSupp ell k Lu hell U a Lam
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  obtain ⟨A, hQA, hin⟩ := AdalyFormal.GenuineU1.Gen.firstTerm_core P hG hN (ContinuousLinearMap.adjoint P.tau B)
  set x : BondFnL2 (scaleUp ell k Lu) := Wop P.G U a (iE P.G A) with hx
  have hWW : Wop P.G U a x = x := Wop_idem P.G hOm U a hu _
  have hQx : (bondSectorOf P.G U).Qfull x = ContinuousLinearMap.adjoint P.tau B := by
    rw [hx, Qfull_Wop P.G U a (bondSectorOf P.G U) hu hB0]
    exact hQA
  set X := ⟪x, Delta P.G U x⟫ with hXdef
  -- the mass of the U-minimiser and of x
  have hmassA : ⟪A, P.data.Mass A⟫ = a * (ell : ℝ) ^ k * ‖B‖ ^ 2 := by
    rw [AdalyFormal.GenuineU1.Gen.mass_inner P hFS A, hQA, AdalyFormal.GenuineU1.Gen.tau_adj_norm P hFS B]
  -- the form of A
  have hDpiA : ⟪A, P.data.Dpi A⟫ = X := by
    have h1 : ⟪A, P.data.Dpi A⟫ = ⟪iE P.G A, DpiFull P.G P.U P.a (iE P.G A)⟫ := by
      show ⟪A, (pE P.G) (DpiFull P.G P.U P.a (iE P.G A))⟫ = _
      rw [pE_inner_right]
    rw [h1, inner_DpiFull]
    rfl
  have hGA : ⟪A, P.data.Ginv A⟫ = X + ‖P.data.T A‖ ^ 2 + a * (ell : ℝ) ^ k * ‖B‖ ^ 2 := by
    rw [BaseDataS.inner_Ginv, hDpiA, hmassA]
  -- x as an element of E₀
  set x' : ↥(bondSupp P.G) := ⟨x, mem_bondSupp_PU ell k Lu hell U a Lam x⟩ with hx'
  have hix : iE P.G x' = x := rfl
  have hDpix : ⟪x', P.data.Dpi x'⟫ = X := by
    have h1 : ⟪x', P.data.Dpi x'⟫ = ⟪iE P.G x', DpiFull P.G P.U P.a (iE P.G x')⟫ := by
      show ⟪x', (pE P.G) (DpiFull P.G P.U P.a (iE P.G x'))⟫ = _
      rw [pE_inner_right]
    rw [h1, hix, inner_DpiFull]
    have hw : x - gradL2 U (Gp P.G U a (Rproj P.G U (gradAdj U x))) = x := by
      rw [← Wop_apply]; exact hWW
    show ⟪x - gradL2 U (Gp P.G U a (Rproj P.G U (gradAdj U x))),
      Delta P.G U (x - gradL2 U (Gp P.G U a (Rproj P.G U (gradAdj U x))))⟫ = X
    rw [hw]
  have hTx : P.data.T x' = 0 := by
    show Tfull P.G U (iE P.G x') = 0
    rw [hix, hx]
    exact AdalyFormal.SliceCoerc.slice_of_Wop P.G hOm U a hu _
  have hmassx : ⟪x', P.data.Mass x'⟫ = a * (ell : ℝ) ^ k * ‖B‖ ^ 2 := by
    rw [AdalyFormal.GenuineU1.Gen.mass_inner P hFS x']
    have : P.data.Q x' = ContinuousLinearMap.adjoint P.tau B := by
      show (bondSectorOf P.G U).Qfull (iE P.G x') = _
      rw [hix]; exact hQx
    rw [this, AdalyFormal.GenuineU1.Gen.tau_adj_norm P hFS B]
  have hGx : ⟪x', P.data.Ginv x'⟫ = X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2 := by
    rw [BaseDataS.inner_Ginv, hDpix, hTx, hmassx]; simp
  have hnx : ‖x'‖ = ‖x‖ := rfl
  have hcx : ‖x‖ ^ 2 ≤ C0 * (X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2) := by
    rw [← hnx, ← hGx]; exact hcoer x'
  refine ⟨x, hQx, hcx, ?_⟩
  -- G₁⁻¹ = G⁻¹ − Δ⁽²⁾
  have hEq : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  have hG1A : ⟪A, P.G1inv A⟫ = ⟪A, P.data.Ginv A⟫ - ⟪A, P.data.Delta2 P.data_laws A⟫ := by
    rw [hEq, ContinuousLinearMap.sub_apply, inner_sub_right]
  have hcA := hcoer A
  have hGA0 : 0 ≤ ⟪A, P.data.Ginv A⟫ := by
    by_contra hneg
    push_neg at hneg
    have h1 : C0 * ⟪A, P.data.Ginv A⟫ < 0 := mul_neg_of_pos_of_neg hC0 hneg
    linarith [sq_nonneg ‖A‖]
  have hlow : (1 - ε') * ⟪A, P.data.Ginv A⟫ ≤ ⟪A, P.G1inv A⟫ := by
    rw [hG1A]
    have h1 : ⟪A, P.data.Delta2 P.data_laws A⟫ ≤ ε' * ⟪A, P.data.Ginv A⟫ := le_trans (le_abs_self _) (hD2f A)
    nlinarith
  have hT0 := sq_nonneg ‖P.data.T A‖
  have hlow2 : (1 - ε') * (X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2) ≤ ⟪A, P.G1inv A⟫ := by
    have : (1 - ε') * (X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2) ≤ (1 - ε') * ⟪A, P.data.Ginv A⟫ := by
      rw [hGA]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  -- genForm
  have hη : P.eta = ((ell : ℝ) ^ k)⁻¹ := rfl
  have hJ' : -(2 * (εJ * ‖B‖ ^ 2)) ≤ -(2 * ⟪P.H1in (P.D2in B), P.Jf⟫) := by
    have := le_abs_self ⟪P.H1in (P.D2in B), P.Jf⟫
    linarith
  have hBB : ⟪B, B⟫ = ‖B‖ ^ 2 := real_inner_self_eq_norm_sq B
  unfold GenP.genForm GenP.firstTerm
  rw [hin, hη, hBB]
  have hmul := mul_le_mul_of_nonneg_left hlow2 (inv_nonneg.mpr hn.le)
  have e1 : ((ell : ℝ) ^ k)⁻¹ * ((1 - ε') * (X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2))
      = (1 - ε') * (X / (ell : ℝ) ^ k) + (1 - ε') * a * ‖B‖ ^ 2 := by
    field_simp
  rw [e1] at hmul
  nlinarith

theorem units_PU_f (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (C0 ε' : ℝ) (hC0 : 0 < C0) (hε' : ε' < 1)
    (hcoer : ∀ y : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      ‖y‖ ^ 2 ≤ C0 * ⟪y, (PU ell k Lu hell U a Lam).data.Ginv y⟫)
    (hD2f : ∀ A : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      |⟪A, (PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws A⟫|
        ≤ ε' * ⟪A, (PU ell k Lu hell U a Lam).data.Ginv A⟫)
    (hQs : Function.Injective (PU ell k Lu hell U a Lam).data.Qs) :
    IsUnit (PU ell k Lu hell U a Lam).G1inv ∧ IsUnit (GenP.Nmat (PU ell k Lu hell U a Lam)) := by
  set P := PU ell k Lu hell U a Lam with hP
  have hc : ∀ x, (1 / C0) * ‖x‖ ^ 2 ≤ ⟪x, P.data.Ginv x⟫ := by
    intro x
    have := hcoer x
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC0]; linarith
  have hEq : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  have hco : ∀ x, ((1 - ε') * (1 / C0)) * ‖x‖ ^ 2 ≤ ⟪x, P.G1inv x⟫ := by
    intro x
    rw [hEq, ContinuousLinearMap.sub_apply, inner_sub_right]
    have h1 := hD2f x
    have h2 := hc x
    have h3 : ⟪x, P.data.Delta2 P.data_laws x⟫ ≤ ε' * ⟪x, P.data.Ginv x⟫ := le_trans (le_abs_self _) h1
    have h4 : 0 ≤ 1 - ε' := by linarith
    have h5 : (1 - ε') * ((1 / C0) * ‖x‖ ^ 2) ≤ (1 - ε') * ⟪x, P.data.Ginv x⟫ := mul_le_mul_of_nonneg_left h2 h4
    nlinarith
  have hpos : 0 < (1 - ε') * (1 / C0) := by
    apply mul_pos (by linarith); positivity
  have hGu : IsUnit P.G1inv := by
    have hinj : Function.Injective P.G1inv := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h := hco x
      rw [hx, inner_zero_right] at h
      have : ‖x‖ ^ 2 ≤ 0 := by
        by_contra hh; push_neg at hh; nlinarith
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
    exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := (P.G1inv : ↥(bondSupp P.G) →ₗ[ℝ] ↥(bondSupp P.G)))).mp hinj⟩
  exact ⟨hGu, P.data.QG1Qs_isUnit P.G1inv_spec hpos hco hQs⟩

#print axioms u_side_f
#print axioms units_PU_f

end AdalyFormal.DLayer
