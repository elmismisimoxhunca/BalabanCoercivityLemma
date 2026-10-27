import TLz6a
import TL3d

/-!
# TL6b -- plaquette cover; curl, plaquette mask, `D*χ_P D`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantLM_L2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (curlAdjoint)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR6

/-- plaquette cover -/
def covP {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) :
    Cov (DeckIdx Lt L) (PeriodicLatticePlaquette Lt) (PeriodicLatticePlaquette L) := (covS h).prodR PeriodicPlaquetteDirections

theorem covP_pi {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) : (covP h).π = phiP h (fun _ => 0) := by
  funext p; simp only [covP, Cov.prodR, covS, phiP, projS_eq_phiS]

theorem covP_tau {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) :
    ((covP h).τ d : PeriodicLatticePlaquette Lt → PeriodicLatticePlaquette Lt) =
      phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) := by
  funext p; simp only [covP, Cov.prodR, covS, phiP, tauS_eq_phiS]; rfl

theorem curl_nat_L2 {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (U : Cfg L) (A : BondFnL2 L) :
    curlCovariantCLM_L2 (pullCfg h o U) (liftF (phiE h o) A) = liftF (phiP h o) (curlCovariantCLM_L2 U A) := by
  have hA : A = WithLp.toLp 2 (WithLp.ofLp A) := rfl
  have hB : liftF (phiE h o) A = WithLp.toLp 2 (pullBond h o (WithLp.ofLp A)) := rfl
  rw [hB]
  have h1 := AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2_toLp (pullCfg h o U) (pullBond h o (WithLp.ofLp A))
  rw [h1, hA]
  have h2 := AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2_toLp U (WithLp.ofLp A)
  simp only [WithLp.ofLp_toLp] at h2
  rw [h2]
  refine PiLp.ext (fun p => ?_)
  simp only [liftF_apply, WithLp.ofLp_toLp]
  exact curl_nat h o U p (WithLp.ofLp A)

theorem phiS_tau0 {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (x : PeriodicLatticeSite Lt) :
    phiS h (fun _ => 0) (phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) x) = phiS h (fun _ => 0) x := by
  funext μ
  apply Fin.ext
  simp only [phiS_val]
  rw [← Nat.mod_add_mod _ (L μ + 1), Nat.mod_mod_of_dvd _ (h μ), Nat.mod_add_mod, Nat.add_zero, Nat.add_mul_mod_self_right]
  simp

theorem phiP_tau0 {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (p : PeriodicLatticePlaquette Lt) :
    phiP h (fun _ => 0) (phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) p) = phiP h (fun _ => 0) p := by
  simp only [phiP, phiS_tau0]

theorem phiE_tau0 {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (d : DeckIdx Lt L) (e : PeriodicLatticeEdge Lt) :
    phiE h (fun _ => 0) (phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) e) = phiE h (fun _ => 0) e := by
  simp only [phiE, phiS_tau0]

theorem desc_curl {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : Cfg L) :
    Desc (covE h) (covP h) (curlCovariantCLM_L2 U) (curlCovariantCLM_L2 (pullCfg h (fun _ => 0) U)) := by
  haveI := deckIdx_nonempty h
  refine desc_of_nat_phi (covE h) (covP h) _ _ (phiE h (fun _ => 0)) (phiP h (fun _ => 0))
    (fun d => phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)))
    (fun d => phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (covE_pi h) (covP_pi h)
    (fun d => covE_tau h d) (fun d => covP_tau h d) (fun f => curl_nat_L2 h _ U f) (fun d f => ?_)
  have := curl_nat_L2 (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (pullCfg h (fun _ => 0) U) f
  rwa [pullCfg_tau] at this

open Classical in
theorem plaqMask_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (P : Set (PeriodicLatticePlaquette L))
    (f : PlaqFnL2 L) :
    plaqMask (phiP h o ⁻¹' P) (liftF (phiP h o) f) = liftF (phiP h o) (plaqMask P f) := by
  refine PiLp.ext (fun p => ?_)
  simp only [plaqMask_apply, liftF_apply]
  rfl

open Classical in
theorem desc_plaqMask {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (P : Set (PeriodicLatticePlaquette L)) :
    Desc (covP h) (covP h) (LinearMap.toContinuousLinearMap (plaqMask P))
      (LinearMap.toContinuousLinearMap (plaqMask (phiP h (fun _ => 0) ⁻¹' P))) := by
  haveI := deckIdx_nonempty h
  refine desc_of_nat_phi (covP h) (covP h) _ _ (phiP h (fun _ => 0)) (phiP h (fun _ => 0))
    (fun d => phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)))
    (fun d => phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (covP_pi h) (covP_pi h)
    (fun d => covP_tau h d) (fun d => covP_tau h d) (fun f => plaqMask_nat h _ P f) (fun d f => ?_)
  have := plaqMask_nat (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (phiP h (fun _ => 0) ⁻¹' P) f
  have hinv : phiP (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) ⁻¹' (phiP h (fun _ => 0) ⁻¹' P) =
      phiP h (fun _ => 0) ⁻¹' P := by
    ext p; simp only [Set.mem_preimage, phiP_tau0]
  rwa [hinv] at this

end AdalyFormal.Thin
