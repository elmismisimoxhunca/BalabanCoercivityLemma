import TL12a

/-!
# TL12b -- `Q` (`QfullOf`) descends
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2

section qf
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

/-- index map of `𝔅` induced by a bond map respecting the `Λ_j`-bond sets -/
def bidxMap (ell k : ℕ) {L' L : PeriodicLatticeExtent} (S' : Tower L') (S : Tower L) (φ : Bond L' → Bond L)
    (hφ : ∀ j : Fin (k + 1), ∀ b, b ∈ bondsLam (geomOf ell k S') j → φ b ∈ bondsLam (geomOf ell k S) j) :
    BIdx (geomOf ell k S') → BIdx (geomOf ell k S) := fun p => ⟨p.1, ⟨φ p.2.1, hφ p.1 p.2.1 p.2.2⟩⟩

theorem bHφ_pi (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) :
    ∀ j : Fin (k + 1), ∀ b, b ∈ bondsLam (geomOf ell k (towerPull h (fun _ => 0) S)) j →
      phiE h (fun _ => 0) b ∈ bondsLam (geomOf ell k S) j :=
  fun j b hb => (bondsLam_iff hp hell (Nat.lt_succ_iff.mp j.2) b).mp hb

theorem bHφ_tau (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (d : DeckIdx Lt L) :
    ∀ j : Fin (k + 1), ∀ b, b ∈ bondsLam (geomOf ell k (towerPull h (fun _ => 0) S)) j →
      phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) b ∈ bondsLam (geomOf ell k (towerPull h (fun _ => 0) S)) j := by
  intro j b hb
  have := (bondsLam_iff (S := towerPull h (fun _ => 0) S) (phiOK_tau h hp d) hell (Nat.lt_succ_iff.mp j.2) b).mp
  rw [towerPull_tau h S d] at this
  exact this hb

open Classical in
theorem covBIdx_pi (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) :
    (covBIdx h S hp hell).π = bidxMap ell k (towerPull h (fun _ => 0) S) S (phiE h (fun _ => 0)) (bHφ_pi h hp hell S) := by
  funext p
  obtain ⟨j, b, hb⟩ := p
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact congrFun (covE_pi h) b

open Classical in
theorem covBIdx_tau (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (d : DeckIdx Lt L) :
    ⇑((covBIdx h S hp hell).τ d) = bidxMap ell k (towerPull h (fun _ => 0) S) (towerPull h (fun _ => 0) S)
      (phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (bHφ_tau h hp hell S d) := by
  funext p
  obtain ⟨j, b, hb⟩ := p
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact congrFun (covE_tau h d) b

theorem QfullOf_apply {L' : PeriodicLatticeExtent} (G : TowerGeom L') (U : Cfg L') (A : BondFnL2 L') (p : BIdx G) :
    QfullOf G U A p = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl

theorem QfullOf_nat {o : Fin 3 → ℕ} (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (hreg : JetReg ell k (towerPull h o S) (UbarTower su2LogExp ell (pullCfg h o U))) (A : BondFnL2 L) (p : BIdx (geomOf ell k (towerPull h o S))) :
    QfullOf (geomOf ell k (towerPull h o S)) (pullCfg h o U) (liftF (phiE h o) A) p =
      QfullOf (geomOf ell k S) U A
        (bidxMap ell k (towerPull h o S) S (phiE h o)
          (fun j b hb => (bondsLam_iff hp hell (Nat.lt_succ_iff.mp j.2) b).mp hb) p) := by
  obtain ⟨j, b, hb⟩ := p
  have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.2
  have hside : ∀ μ, ell ^ (j : ℕ) ∣ Lt μ + 1 := fun μ => ((phiOK_le (hp := hp) hj).side μ).trans (h μ)
  have hal : Aligned (ell ^ (j : ℕ)) b.1 := bondsLam_aligned hside hb
  rw [QfullOf_apply, QfullOf_apply]
  show _ • _ = _ • _
  congr 1
  exact QlinB_nat h hp hell S U hj hreg A hal hb

theorem QfullOf_nat' {o : Fin 3 → ℕ} (hp : PhiOK h o (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (St : Tower Lt) (hSt : St = towerPull h o S) (Ut : Cfg Lt) (hUt : Ut = pullCfg h o U)
    (hreg : JetReg ell k St (UbarTower su2LogExp ell Ut)) (hφ : ∀ j : Fin (k + 1), ∀ b, b ∈ bondsLam (geomOf ell k St) j →
      phiE h o b ∈ bondsLam (geomOf ell k S) j)
    (A : BondFnL2 L) (p : BIdx (geomOf ell k St)) :
    QfullOf (geomOf ell k St) Ut (liftF (phiE h o) A) p =
      QfullOf (geomOf ell k S) U A (bidxMap ell k St S (phiE h o) hφ p) := by
  subst hSt hUt
  exact QfullOf_nat h hp hell S U hreg A p

open Classical in
theorem desc_QfullOf [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (hreg : JetReg ell k (towerPull h (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg h (fun _ => 0) U))) :
    Desc (covE h) (covBIdx h S hp hell) (QfullOf (geomOf ell k S) U)
      (QfullOf (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) := by
  refine desc_of_nat_phi (covE h) (covBIdx h S hp hell) _ _ (phiE h (fun _ => 0))
    (bidxMap ell k (towerPull h (fun _ => 0) S) S (phiE h (fun _ => 0)) (bHφ_pi h hp hell S))
    (fun d => phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)))
    (fun d => bidxMap ell k (towerPull h (fun _ => 0) S) (towerPull h (fun _ => 0) S)
      (phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (bHφ_tau h hp hell S d))
    (covE_pi h) (covBIdx_pi h hp hell S) (fun d => covE_tau h d) (fun d => covBIdx_tau h hp hell S d)
    (fun f => ?_) (fun d f => ?_)
  · refine PiLp.ext (fun p => ?_)
    rw [liftF_apply]
    exact QfullOf_nat' h hp hell S U _ rfl _ rfl hreg (bHφ_pi h hp hell S) f p
  · refine PiLp.ext (fun p => ?_)
    rw [liftF_apply]
    exact QfullOf_nat' (Covers.refl Lt) (phiOK_tau h hp d) hell (towerPull h (fun _ => 0) S) (pullCfg h (fun _ => 0) U)
      (towerPull h (fun _ => 0) S) (towerPull_tau h S d).symm (pullCfg h (fun _ => 0) U) (pullCfg_tau h d U).symm
      hreg (bHφ_tau h hp hell S d) f p

end qf



end AdalyFormal.Thin
