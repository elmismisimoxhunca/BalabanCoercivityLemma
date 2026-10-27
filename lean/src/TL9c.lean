import TL9b

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section lam2
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem covLamIdx_pi (hp : PhiOK h (fun _ => 0) (ell ^ k)) (S : Tower L) :
    (covLamIdx h S hp).π = lamMap ell k (towerPull h (fun _ => 0) S) S (phiS h (fun _ => 0)) (lamHφ_pi h hp S) := by
  funext p
  obtain ⟨j, y, hy⟩ := p
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact projS_zero h y

theorem covLamIdx_tau (hp : PhiOK h (fun _ => 0) (ell ^ k))
    (hpd : ∀ d : DeckIdx Lt L, PhiOK (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (ell ^ k)) (S : Tower L) (d : DeckIdx Lt L) :
    ⇑((covLamIdx h S hp).τ d) = lamMap ell k (towerPull h (fun _ => 0) S) (towerPull h (fun _ => 0) S)
      (phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (lamHφ_tau h hp hpd S d) := by
  funext p
  obtain ⟨j, y, hy⟩ := p
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact congrFun (tauS_eq_phiS h d) y

theorem phiOK_tau (hp : PhiOK h (fun _ => 0) (ell ^ k)) (d : DeckIdx Lt L) :
    PhiOK (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (ell ^ k) :=
  ⟨fun μ => (hp.side μ).trans (h μ), fun μ => Dvd.dvd.mul_left (hp.side μ) _⟩

end lam2

section stack
variable {L : PeriodicLatticeExtent}

/-- the stack of `Q'_j(U) y`, `y ∈ Λ_j` -/
noncomputable def QlevStack (G : TowerGeom L) (U : Cfg L) : SiteL2 L →L[ℝ] PiLp 2 (fun _ : LamIdx G => SuTwo) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun p : LamIdx G => Qlev G U p.1 p.2.1 f)
      map_add' := fun f g => by ext p; simp
      map_smul' := fun c f => by ext p; simp }

theorem QlevStack_apply (G : TowerGeom L) (U : Cfg L) (f : SiteL2 L) (p : LamIdx G) :
    QlevStack G U f p = Qlev G U p.1 p.2.1 f := rfl

end stack

section stack2
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem desc_QlevStack [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) :
    Desc (covS h) (covLamIdx h S hp) (QlevStack (geomOf ell k S) U)
      (QlevStack (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) := by
  have hpd := fun d => phiOK_tau h hp d
  refine desc_of_nat_phi (covS h) (covLamIdx h S hp) _ _ (phiS h (fun _ => 0))
    (lamMap ell k (towerPull h (fun _ => 0) S) S (phiS h (fun _ => 0)) (lamHφ_pi h hp S))
    (fun d => phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)))
    (fun d => lamMap ell k (towerPull h (fun _ => 0) S) (towerPull h (fun _ => 0) S)
      (phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (lamHφ_tau h hp hpd S d))
    (covS_pi h) (covLamIdx_pi h hp S) (fun d => covS_tau h d) (fun d => covLamIdx_tau h hp hpd S d)
    (fun f => ?_) (fun d f => ?_)
  · refine PiLp.ext (fun p => ?_)
    rw [QlevStack_apply]
    show _ = (QlevStack (geomOf ell k S) U f) (lamMap ell k (towerPull h (fun _ => 0) S) S (phiS h (fun _ => 0)) (lamHφ_pi h hp S) p)
    rw [QlevStack_apply]
    exact Qlev_nat hp hell S U (Nat.lt_succ_iff.mp p.1.2) f p.2.2
  · refine PiLp.ext (fun p => ?_)
    rw [QlevStack_apply]
    show _ = (QlevStack (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) f)
      (lamMap ell k (towerPull h (fun _ => 0) S) (towerPull h (fun _ => 0) S)
        (phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) (lamHφ_tau h hp hpd S d) p)
    rw [QlevStack_apply]
    have := Qlev_nat (hpd d) hell (towerPull h (fun _ => 0) S) (pullCfg h (fun _ => 0) U) (Nat.lt_succ_iff.mp p.1.2) f
      (y := p.2.1) (by rw [towerPull_tau h S d]; exact p.2.2)
    rw [towerPull_tau h S d, pullCfg_tau] at this
    exact this

end stack2

end AdalyFormal.Thin
