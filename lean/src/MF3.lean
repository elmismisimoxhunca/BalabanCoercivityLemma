import RKF
import GN3
import ZGU1D
import ZGU1F

/-!
# MF3 -- the U side of the M0 route, on the GENUINE objects of the frozen statement (full tower, `Ω₀ = ` torus, any `U`).

`P = ⟨ell, k, Lu, _, fullTower ell k Lu, U, a, Lam⟩` (= `gparams ell k Lu hell (fullTower ell k Lu) U a Lam`).
Given `IsUnit G₁⁻¹`, `IsUnit N` (so `genForm` is the printed `(QG₁Q*)⁻¹` form), the site unit `hu`, `B0` (`Q_U D_U ν = 0` on `N(Q'_U)`),
a coercivity constant `C0 > 0` of `G⁻¹` on `E₀`, `‖Δ⁽²⁾‖ ≤ ε2` with `ε2 C0 ≤ 1`, and `|⟨H₁D̃⁽²⁾B, J⟩| ≤ εJ ‖B‖²`:
there is a fine field `x` (= `W_U A`, `A` the U-minimiser of `firstTerm_core`) with
  (Q)  `Q_U x = τ* B`                                   (the constraint survives the slice projection: B0),
  (C)  `‖x‖² ≤ C0 (⟨x, Δ_U x⟩ + a n ‖B‖²)`              (coercivity at `x`: `T x = 0`, mass of `x` = `a n ‖B‖²`),
  (G)  `(1 − ε2 C0) ⟨x,Δ_U x⟩ / n − (ε2 C0 a + 2 εJ) ‖B‖² ≤ genForm(B)`   (mass term cancels `−a‖B‖²` exactly).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M0Finish

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG (GenP.genForm GenP.firstTerm GenP.Nmat)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

/-- the full-tower genuine parameters at a general `U` -/
abbrev PU (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) : IngrBParams :=
  ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩

theorem PU_Om0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) : (PU ell k Lu hell U a Lam).G.Om0 = Set.univ := by
  simp [PU, IngrBParams.G, geomOf, fullTower]

/-- every fine field lies in `E₀` on the full tower -/
theorem mem_bondSupp_PU (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (x : BondFnL2 (scaleUp ell k Lu)) :
    x ∈ bondSupp (PU ell k Lu hell U a Lam).G := by
  intro b hb
  exact absurd (Or.inl (by rw [PU_Om0]; trivial)) hb

theorem Wop_apply {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (z : BondFnL2 L) :
    Wop G U a z = z - gradL2 U (Gp G U a (Rproj G U (gradAdj U z))) := by
  simp [Wop]

theorem Wop_idem {L : PeriodicLatticeExtent} (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (y : BondFnL2 L) :
    Wop G U a (Wop G U a y) = Wop G U a y := by
  have h0 := AdalyFormal.SliceCoerc.slice_of_Wop G hOm U a hu y
  rw [Wop_apply G U a (Wop G U a y), h0, map_zero, map_zero, sub_zero]

theorem Qfull_Wop {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (hB0 : ∀ ν ∈ NQp G U, S.Qfull (gradL2 U ν) = 0) (y : BondFnL2 L) :
    S.Qfull (Wop G U a y) = S.Qfull y := by
  have hlam := (AdalyFormal.SliceCoerc.Gp_Rproj_mem G U a hu (gradAdj U y)).1
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_sub, hB0 _ hlam, sub_zero]

/-- **the U side** -/
theorem u_side (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (hu : IsUnit (DelpA (PU ell k Lu hell U a Lam).G U a + (1 - siteMask (PU ell k Lu hell U a Lam).G.Om0)))
    (hB0 : ∀ ν ∈ NQp (PU ell k Lu hell U a Lam).G U,
      (bondSectorOf (PU ell k Lu hell U a Lam).G U).Qfull (gradL2 U ν) = 0)
    (hG : IsUnit (PU ell k Lu hell U a Lam).G1inv) (hN : IsUnit (GenP.Nmat (PU ell k Lu hell U a Lam)))
    (C0 ε2 εJ : ℝ) (hC0 : 0 < C0) (hε2 : 0 ≤ ε2) (hε2C : ε2 * C0 ≤ 1)
    (hcoer : ∀ y : ↥(bondSupp (PU ell k Lu hell U a Lam).G),
      ‖y‖ ^ 2 ≤ C0 * ⟪y, (PU ell k Lu hell U a Lam).data.Ginv y⟫)
    (hD2 : ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖ ≤ ε2)
    (B : BondFnL2 Lu)
    (hJ : |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in B),
        (PU ell k Lu hell U a Lam).Jf⟫| ≤ εJ * ‖B‖ ^ 2) :
    ∃ x : BondFnL2 (scaleUp ell k Lu),
      (bondSectorOf (PU ell k Lu hell U a Lam).G U).Qfull x
          = ContinuousLinearMap.adjoint (PU ell k Lu hell U a Lam).tau B ∧
      ‖x‖ ^ 2 ≤ C0 * (⟪x, Delta (PU ell k Lu hell U a Lam).G U x⟫ + a * (ell : ℝ) ^ k * ‖B‖ ^ 2) ∧
      (1 - ε2 * C0) * (⟪x, Delta (PU ell k Lu hell U a Lam).G U x⟫ / (ell : ℝ) ^ k)
          - (ε2 * C0 * a + 2 * εJ) * ‖B‖ ^ 2
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
  have hD2A : |⟪A, P.data.Delta2 P.data_laws A⟫| ≤ ε2 * ‖A‖ ^ 2 := by
    calc |⟪A, P.data.Delta2 P.data_laws A⟫| ≤ ‖A‖ * ‖P.data.Delta2 P.data_laws A‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖A‖ * (‖P.data.Delta2 P.data_laws‖ * ‖A‖) :=
          mul_le_mul_of_nonneg_left ((P.data.Delta2 P.data_laws).le_opNorm A) (norm_nonneg _)
      _ ≤ ‖A‖ * (ε2 * ‖A‖) := by gcongr
      _ = ε2 * ‖A‖ ^ 2 := by ring
  have hcA := hcoer A
  have hGA0 : 0 ≤ ⟪A, P.data.Ginv A⟫ := by
    by_contra hneg
    push_neg at hneg
    have h1 : C0 * ⟪A, P.data.Ginv A⟫ < 0 := mul_neg_of_pos_of_neg hC0 hneg
    linarith [sq_nonneg ‖A‖]
  have hlow : (1 - ε2 * C0) * ⟪A, P.data.Ginv A⟫ ≤ ⟪A, P.G1inv A⟫ := by
    rw [hG1A]
    have h1 : ⟪A, P.data.Delta2 P.data_laws A⟫ ≤ ε2 * ‖A‖ ^ 2 := le_trans (le_abs_self _) hD2A
    have h2 : ε2 * ‖A‖ ^ 2 ≤ ε2 * (C0 * ⟪A, P.data.Ginv A⟫) := mul_le_mul_of_nonneg_left hcA hε2
    nlinarith
  have hT0 := sq_nonneg ‖P.data.T A‖
  have hlow2 : (1 - ε2 * C0) * (X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2) ≤ ⟪A, P.G1inv A⟫ := by
    have : (1 - ε2 * C0) * (X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2) ≤ (1 - ε2 * C0) * ⟪A, P.data.Ginv A⟫ := by
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
  have e1 : ((ell : ℝ) ^ k)⁻¹ * ((1 - ε2 * C0) * (X + a * (ell : ℝ) ^ k * ‖B‖ ^ 2))
      = (1 - ε2 * C0) * (X / (ell : ℝ) ^ k) + (1 - ε2 * C0) * a * ‖B‖ ^ 2 := by
    field_simp
  rw [e1] at hmul
  nlinarith

#print axioms PU_Om0
#print axioms mem_bondSupp_PU
#print axioms Wop_apply
#print axioms Wop_idem
#print axioms Qfull_Wop
#print axioms u_side

end AdalyFormal.M0Finish
