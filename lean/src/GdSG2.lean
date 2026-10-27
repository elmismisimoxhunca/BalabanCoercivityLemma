import GdGapAll

/-!
# GdSG2 -- the full-guard literal inequality `InstIneqSG2` on the boundary-twist family, from the localised headline at the flat point.

Chain (all steps are Lean theorems below):
* `genFormS_theta` (GdFam): on the family `genFormS B = η⟨τ*B, N⁻¹ τ*B⟩ - a⟨B,B⟩`, `N = Q G Q*`.
* `GdAlg.compare_firstterm_N` (a form of `compare_inverse_forms`): with `x₀ = Ginv(θ)⁻¹ Q* N⁻¹ τ*B` (stationary point; `Q x₀ = τ*B` has no level-0 part, so `x₀` vanishes on the level-0 bonds),
  `⟨b, N_loc⁻¹ b⟩ ≤ ⟨x₀, Ginv_loc x₀⟩ ≤ ⟨x₀, Ginv_lit(0) x₀⟩ = ⟨x₀, Ginv_lit(θ) x₀⟩ = ⟨b, N_lit(θ)⁻¹ b⟩`.
  (`Ginv_loc ≤ Ginv_lit(0)` at the flat point: `Ginv_form_mono_flat`; `Ginv_lit(θ) x₀ = Ginv_lit(0) x₀`: `Fth_theta_apply_eq`; the localised side is the
  Dirichlet principle for the PSD form `Ginv_loc`.)
* `genC` is the same on `U_θ` and on the flat point (`genC_congr`), `Q` is the same (`Qfull_theta_flat`).
* The localised headline at the flat point (`P428Target8`, proved) supplies `γ₀ E ≤ genForm_loc`.  If the localised `Ginv` or `N` were not units, the localised
  form is the junk value `-a‖B‖²` and the same inequality forces the energy (hence the test field) to vanish.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

section firstterm

/-- `Q` of the twist data is that of the flat data. -/
theorem Q_twist_eq_flat {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) (sD sJ sD' sJ' : PlaqSel) :
    (dataS sD sJ (Pth ell k Lu hell0 S a Lam θ)).Q = (dataS sD' sJ' (Pth ell k Lu hell0 S a Lam 0)).Q := by
  have e1 := dataS_Q_eq sD sJ (Pth ell k Lu hell0 S a Lam θ)
  have e2 := dataS_Q_eq sD' sJ' (Pth ell k Lu hell0 S a Lam 0)
  have h : QfullOf (geomOf ell k S) (Uth (S.Om 0) θ) = QfullOf (geomOf ell k S) (Uth (S.Om 0) 0) :=
    (Qfull_theta_flat (L := scaleUp ell k Lu) hS hell hroom θ).trans
        (Qfull_theta_flat (L := scaleUp ell k Lu) hS hell hroom 0).symm
  have h2 : (QfullOf (geomOf ell k S) (Uth (S.Om 0) θ)).comp (iE (geomOf ell k S)) =
      (QfullOf (geomOf ell k S) (Uth (S.Om 0) 0)).comp (iE (geomOf ell k S)) := by rw [h]
  exact e1.trans (h2.trans e2.symm)

theorem Qs_twist_eq_flat {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) (sD sJ sD' sJ' : PlaqSel) :
    (dataS sD sJ (Pth ell k Lu hell0 S a Lam θ)).Qs = (dataS sD' sJ' (Pth ell k Lu hell0 S a Lam 0)).Qs := by
  have e1 := dataS_Qs_eq sD sJ (Pth ell k Lu hell0 S a Lam θ)
  have e2 := dataS_Qs_eq sD' sJ' (Pth ell k Lu hell0 S a Lam 0)
  have h : QfullOf (geomOf ell k S) (Uth (S.Om 0) θ) = QfullOf (geomOf ell k S) (Uth (S.Om 0) 0) :=
    (Qfull_theta_flat (L := scaleUp ell k Lu) hS hell hroom θ).trans
        (Qfull_theta_flat (L := scaleUp ell k Lu) hS hell hroom 0).symm
  have h2 : ContinuousLinearMap.adjoint ((QfullOf (geomOf ell k S) (Uth (S.Om 0) θ)).comp (iE (geomOf ell k S))) =
      ContinuousLinearMap.adjoint ((QfullOf (geomOf ell k S) (Uth (S.Om 0) 0)).comp (iE (geomOf ell k S))) := by rw [h]
  exact e1.trans (h2.trans e2.symm)

/-- **first-term comparison**: the literal first term at `θ` dominates the localised first term at the flat point. -/
theorem firstTerm_twist_ge (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hk : 1 ≤ k) (hell : 2 ≤ ell)
    (hroom : 17 * ell ≤ R * M) {a : ℝ} (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ)
    (hWD : WellDefAt selAll sJ (Pth ell k Lu hell0 S a Lam θ))
    (hu : IsUnit (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Ginv ∧
      IsUnit (GenS.NmatS selIn selIn (Pth ell k Lu hell0 S a Lam 0))) (B : BondFnL2 Lu) :
    GenS.firstTermS selIn selIn (Pth ell k Lu hell0 S a Lam 0) B ≤
      GenS.firstTermS selAll sJ (Pth ell k Lu hell0 S a Lam θ) B := by
  have h3 : 3 ≤ R * M := by omega
  have hN1 := NmatS_eq_QGQs selAll sJ (Pth ell k Lu hell0 S a Lam θ) hS hell0 h3 θ rfl
  have hN2 := NmatS_eq_QGQs selIn selIn (Pth ell k Lu hell0 S a Lam 0) hS hell0 h3 0 rfl
  have hQ' : (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Q = (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Q :=
    (Q_twist_eq_flat hell0 hS hell hroom a Lam θ selAll sJ selIn selIn).symm
  have hQs' : (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Qs = (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Qs :=
    (Qs_twist_eq_flat hell0 hS hell hroom a Lam θ selAll sJ selIn selIn).symm
  have hN₁ : IsUnit (((dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Q.comp
      (Ring.inverse (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv)).comp (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Qs) :=
    hN1 ▸ hWD.2.2
  have hN₂ : IsUnit (((dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Q.comp
      (Ring.inverse (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Ginv)).comp (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Qs) :=
    hN2 ▸ hu.2
  obtain ⟨hQx0, -, -⟩ := Alg.dirichlet_value hWD.1 (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Q_adj hN₁
    (ContinuousLinearMap.adjoint (Pth ell k Lu hell0 S a Lam θ).tau B)
  have hA0 : ∀ β ∈ bondsLam (geomOf ell k S) 0,
      (WithLp.ofLp (iE (geomOf ell k S) (Alg.stat (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv
        (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Q (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Qs
        (ContinuousLinearMap.adjoint (Pth ell k Lu hell0 S a Lam θ).tau B)))) β = 0 := by
    intro β hβ
    have hβ' : β ∈ bondsLam (Pth ell k Lu hell0 S a Lam θ).G (((0 : Fin ((Pth ell k Lu hell0 S a Lam θ).G.k + 1)) : Fin _) : ℕ) := hβ
    have h1 := Q_level0_coord selAll sJ (Pth ell k Lu hell0 S a Lam θ)
      (Alg.stat (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Q
        (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Qs (ContinuousLinearMap.adjoint (Pth ell k Lu hell0 S a Lam θ).tau B)) β hβ'
    rw [hQx0] at h1
    exact h1.symm.trans (adjoint_tau_level0 (Pth ell k Lu hell0 S a Lam θ) hk B β hβ')
  have hle_gen : ∀ x0 : ↥(bondSupp (geomOf ell k S)),
      (∀ β ∈ bondsLam (geomOf ell k S) 0, (WithLp.ofLp (iE (geomOf ell k S) x0)) β = 0) →
      ⟪x0, (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Ginv x0⟫ ≤
        ⟪x0, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv x0⟫ := by
    intro x0 hx0
    have e1 := Ginv_form_mono_flat hell0 a Lam sJ selIn x0
    have e2 : Fth sJ ell k Lu hell0 S a Lam θ x0 = Fth sJ ell k Lu hell0 S a Lam 0 x0 :=
      Fth_theta_apply_eq sJ hell0 hS hell hroom a Lam θ x0 hx0
    have e3 : ⟪x0, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv x0⟫ =
        ⟪x0, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam 0)).Ginv x0⟫ :=
      congrArg (fun y => ⟪x0, y⟫) e2
    exact e1.trans_eq e3.symm
  have hle := hle_gen _ hA0
  have key := Alg.compare_firstterm_N (E := ↥(bondSupp (geomOf ell k S))) (F := FSp (geomOf ell k S)) hQ' hQs' hN1 hN2 hWD.1
    ((dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Ginv_symm (dataS_laws selIn selIn _)) hu.1
    (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Q_adj hWD.2.2 hu.2
    (Ginv_psd_flat hell0 a Lam selIn selIn ha) (ContinuousLinearMap.adjoint (Pth ell k Lu hell0 S a Lam θ).tau B) hle
  unfold GenS.firstTermS
  exact mul_le_mul_of_nonneg_left key (IngrBParams.eta_pos _).le

#print axioms Q_twist_eq_flat
#print axioms Qs_twist_eq_flat
#print axioms firstTerm_twist_ge

end firstterm

end AdalyFormal.D1Guarded
