import GdGap2

/-!
# GdGapAll -- `GapAt` on the whole boundary-twist family, given `Q*` injective.
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

/-- on the twist family `N = Q G Q*`. -/
theorem NmatS_eq_QGQs (sD sJ : PlaqSel) (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (h3 : 3 ≤ R * M) (θ : ℝ) (hU : P.U = Uth (P.S.Om 0) θ) :
    GenS.NmatS sD sJ P = ((dataS sD sJ P).Q.comp (Ring.inverse (dataS sD sJ P).Ginv)).comp (dataS sD sJ P).Qs := by
  have h := G1invS_eq_Ginv_theta sD sJ P hS hell h3 θ hU
  unfold GenS.NmatS BaseDataS.G1
  rw [h]

/-- **`GapAt` on the whole boundary-twist family** (every `θ`): given `Q*` injective and `0 ≤ a`.
`Ginv(θ)` restricted to `ker Q` equals `Ginv(0)` (`Fth_theta_apply_eq`), which is positive semidefinite; a unit cannot have a kernel vector. -/
theorem GapAt_twist (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) {a : ℝ}
    (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ)
    (hQs : Function.Injective (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Qs) :
    GapAt selAll sJ (Pth ell k Lu hell0 S a Lam θ) := by
  have h3 : 3 ≤ R * M := by omega
  rw [GapAt_theta_iff selAll sJ (Pth ell k Lu hell0 S a Lam θ) hS hell0 h3 θ rfl]
  intro hu
  refine isUnit_Q_inv_Qs_of_pos_ker ((dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv_symm
    (dataS_laws selAll sJ _)) hu (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Q_adj hQs ?_
  intro x hx hne
  have hA0 : ∀ b ∈ bondsLam (geomOf ell k S) 0, (WithLp.ofLp (iE (geomOf ell k S) x)) b = 0 := by
    intro b hb
    have hb' : b ∈ bondsLam (Pth ell k Lu hell0 S a Lam θ).G (((0 : Fin ((Pth ell k Lu hell0 S a Lam θ).G.k + 1)) : Fin _) : ℕ) := hb
    have := Q_level0_coord selAll sJ (Pth ell k Lu hell0 S a Lam θ) x b hb'
    rw [hx] at this
    exact this.symm.trans (by simp)
  have heq : Fth sJ ell k Lu hell0 S a Lam θ x = Fth sJ ell k Lu hell0 S a Lam 0 x :=
    Fth_theta_apply_eq sJ hell0 hS hell hroom a Lam θ x hA0
  have hpsd : PSD (Fth sJ ell k Lu hell0 S a Lam 0) := Fth_zero_psd sJ hell0 a Lam ha
  have hform : ⟪x, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv x⟫ = ⟪x, Fth sJ ell k Lu hell0 S a Lam 0 x⟫ := by
    show ⟪x, Fth sJ ell k Lu hell0 S a Lam θ x⟫ = _
    rw [heq]
  by_contra hnpos
  have hle : ⟪x, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv x⟫ ≤ 0 := not_lt.mp hnpos
  have h0 : ⟪x, Fth sJ ell k Lu hell0 S a Lam 0 x⟫ = 0 := le_antisymm (hform ▸ hle) (hpsd x)
  have hker : Fth sJ ell k Lu hell0 S a Lam 0 x = 0 :=
    psd_kernel _ (Fth_symm sJ hell0 a Lam 0) hpsd x h0
  have hker' : (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv x = 0 := by
    show Fth sJ ell k Lu hell0 S a Lam θ x = 0
    rw [heq, hker]
  obtain ⟨u, hu'⟩ := hu
  apply hne
  have : x = (↑u⁻¹ : _ →L[ℝ] _) ((dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv x) := by
    rw [← hu']
    exact (ContinuousLinearMap.ext_iff.mp u.inv_mul x).symm
  rw [this, hker']
  simp

#print axioms NmatS_eq_QGQs
#print axioms GapAt_twist

end AdalyFormal.D1Guarded
