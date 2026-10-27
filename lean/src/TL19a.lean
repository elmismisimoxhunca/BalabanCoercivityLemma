import TL15c
import ZXR2Wire1

/-!
# TL19a -- `τ` (`tauExt`) descends
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section tau
variable {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) (ell k : ℕ) (hell : 0 < ell)

theorem phiS_emb0 (y : PeriodicLatticeSite Lut) :
    phiS (covers_scaleUp ell k hell hu) (fun _ => 0) (embY ell k Lut hell y) = embY ell k Lu hell (phiS hu (fun _ => 0) y) := by
  have := phiS_emb hu ell k hell (fun _ => 0) y
  simpa using this

/-- unit edge cover with the fine deck group -/
noncomputable def covEU : Cov (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) (PeriodicLatticeEdge Lut) (PeriodicLatticeEdge Lu) :=
  (covE hu).reindex (eUnit ell k hell)

theorem covEU_pi : (covEU hu ell k hell).π = phiE hu (fun _ => 0) := covE_pi hu

theorem covEU_tau (d : DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) :
    ((covEU hu ell k hell).τ d : PeriodicLatticeEdge Lut → PeriodicLatticeEdge Lut) =
      phiE (Covers.refl Lut) (fun μ => (d μ).val * (Lu μ + 1)) := by
  funext e
  have := congrFun (covE_tau hu (eUnit ell k hell d)) e
  simpa [covEU, Cov.reindex, eUnit_val] using this

theorem phiS_emb_gen (of ou : Fin 3 → ℕ) (ho : ∀ μ, of μ = ell ^ k * ou μ) (y : PeriodicLatticeSite Lut) :
    phiS (covers_scaleUp ell k hell hu) of (embY ell k Lut hell y) = embY ell k Lu hell (phiS hu ou y) := by
  have : of = fun μ => ell ^ k * ou μ := funext ho
  subst this
  exact phiS_emb hu ell k hell ou y

theorem phiE_emb_gen (of ou : Fin 3 → ℕ) (ho : ∀ μ, of μ = ell ^ k * ou μ) (e : Bond Lut) :
    phiE (covers_scaleUp ell k hell hu) of (unitBondEmb ell k Lut hell e) = unitBondEmb ell k Lu hell (phiE hu ou e) := by
  simp only [phiE, unitBondEmb, phiS_emb_gen hu ell k hell of ou ho]

open Classical in
theorem tauExt_apply {L' : PeriodicLatticeExtent} (G : Tower (scaleUp ell k L')) (f : FSp (geomOf ell k G)) (e : Bond L') :
    tauExt ell k L' hell G f e = if hb : unitBondEmb ell k L' hell e ∈ bondsLam (geomOf ell k G) k
      then WithLp.ofLp f ⟨Fin.last k, ⟨unitBondEmb ell k L' hell e, hb⟩⟩ else 0 := rfl

open Classical in
/-- generic naturality of `τ` for compatible fine/unit pull-backs -/
theorem tauExt_nat (of ou : Fin 3 → ℕ) (ho : ∀ μ, of μ = ell ^ k * ou μ)
    (hp : PhiOK (covers_scaleUp ell k hell hu) of (ell ^ k)) (S : Tower (scaleUp ell k Lu))
    (St : Tower (scaleUp ell k Lut)) (hSt : St = towerPull (covers_scaleUp ell k hell hu) of S)
    (hφ : ∀ j : Fin (k + 1), ∀ b, b ∈ bondsLam (geomOf ell k St) j →
      phiE (covers_scaleUp ell k hell hu) of b ∈ bondsLam (geomOf ell k S) j)
    (f : FSp (geomOf ell k S)) (e : Bond Lut) :
    tauExt ell k Lut hell St (liftF (bidxMap ell k St S (phiE (covers_scaleUp ell k hell hu) of) hφ) f) e =
      tauExt ell k Lu hell S f (phiE hu ou e) := by
  rw [tauExt_apply ell k hell, tauExt_apply ell k hell]
  have hmem : unitBondEmb ell k Lut hell e ∈ bondsLam (geomOf ell k St) k ↔
      unitBondEmb ell k Lu hell (phiE hu ou e) ∈ bondsLam (geomOf ell k S) k := by
    subst hSt
    rw [bondsLam_iff hp hell le_rfl, phiE_emb_gen hu ell k hell of ou ho]
  by_cases hb : unitBondEmb ell k Lut hell e ∈ bondsLam (geomOf ell k St) k
  · have hb' := hmem.mp hb
    rw [dif_pos hb, dif_pos hb']
    have hx : bidxMap ell k St S (phiE (covers_scaleUp ell k hell hu) of) hφ ⟨Fin.last k, ⟨unitBondEmb ell k Lut hell e, hb⟩⟩ =
        (⟨Fin.last k, ⟨unitBondEmb ell k Lu hell (phiE hu ou e), hb'⟩⟩ : BIdx (geomOf ell k S)) :=
      Sigma.subtype_ext rfl (phiE_emb_gen hu ell k hell of ou ho e)
    show f (bidxMap ell k St S (phiE (covers_scaleUp ell k hell hu) of) hφ ⟨Fin.last k, ⟨unitBondEmb ell k Lut hell e, hb⟩⟩) = _
    rw [hx]
  · have hb' : ¬ unitBondEmb ell k Lu hell (phiE hu ou e) ∈ bondsLam (geomOf ell k S) k := fun h => hb (hmem.mpr h)
    rw [dif_neg hb, dif_neg hb']

theorem hf_ho_zero : ∀ μ : Fin 3, (fun _ : Fin 3 => 0) μ = ell ^ k * (fun _ : Fin 3 => 0) μ := fun μ => by simp

open Classical in
theorem desc_tau [Nonempty (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu))]
    (hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)) (S : Tower (scaleUp ell k Lu)) :
    Desc (covBIdx (covers_scaleUp ell k hell hu) S hp hell) (covEU hu ell k hell) (tauExt ell k Lu hell S)
      (tauExt ell k Lut hell (towerPull (covers_scaleUp ell k hell hu) (fun _ => 0) S)) := by
  have hf := covers_scaleUp ell k hell hu
  refine desc_of_nat_phi (covBIdx hf S hp hell) (covEU hu ell k hell) _ _
    (bidxMap ell k (towerPull hf (fun _ => 0) S) S (phiE hf (fun _ => 0)) (bHφ_pi hf hp hell S))
    (phiE hu (fun _ => 0))
    (fun d => bidxMap ell k (towerPull hf (fun _ => 0) S) (towerPull hf (fun _ => 0) S)
      (phiE (Covers.refl (scaleUp ell k Lut)) (fun μ => (d μ).val * (scaleUp ell k Lu μ + 1))) (bHφ_tau hf hp hell S d))
    (fun d => phiE (Covers.refl Lut) (fun μ => (d μ).val * (Lu μ + 1)))
    (covBIdx_pi hf hp hell S) (covEU_pi hu ell k hell) (fun d => covBIdx_tau hf hp hell S d) (fun d => covEU_tau hu ell k hell d)
    (fun f => ?_) (fun d f => ?_)
  · refine PiLp.ext (fun e => ?_)
    rw [liftF_apply]
    exact tauExt_nat hu ell k hell (fun _ => 0) (fun _ => 0) (hf_ho_zero ell k) hp S _ rfl (bHφ_pi hf hp hell S) f e
  · refine PiLp.ext (fun e => ?_)
    rw [liftF_apply]
    have hSt : towerPull hf (fun _ => 0) S = towerPull (covers_scaleUp ell k hell (Covers.refl Lut))
        (fun μ => (d μ).val * (scaleUp ell k Lu μ + 1)) (towerPull hf (fun _ => 0) S) := (towerPull_tau hf S d).symm
    exact tauExt_nat (Covers.refl Lut) ell k hell (fun μ => (d μ).val * (scaleUp ell k Lu μ + 1))
      (fun μ => (d μ).val * (Lu μ + 1)) (fun μ => by rw [scaleUp_add_one ell k hell]; ring)
      (phiOK_tau hf hp d) (towerPull hf (fun _ => 0) S) (towerPull hf (fun _ => 0) S) hSt (bHφ_tau hf hp hell S d) f e

end tau



end AdalyFormal.Thin
