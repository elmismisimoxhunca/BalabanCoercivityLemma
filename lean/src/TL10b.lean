import TL10a

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section nqp
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem nqp_ell [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (f : SiteL2 L) (hf : f ∈ NQp (geomOf ell k S) U) :
    (covS h).ell f ∈ NQp (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show f ((covS h).π x) = 0
    rw [covS_pi]
    exact h1 _ hx
  · have hnat := Qlev_nat hp hell S U hj f hy
    have hell' : (covS h).ell f = liftF (phiS h (fun _ => 0)) f := by
      show liftF (covS h).π f = _
      rw [covS_pi]
    show Qlev _ _ j y ((covS h).ell f) = 0
    rw [hell', hnat]
    exact h2 j hj _ ((lam_iff hp hj y).mp hy)

open Classical in
theorem nqp_sig [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (f : SiteL2 Lt) (hf : f ∈ NQp (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) :
    (covS h).sig f ∈ NQp (geomOf ell k S) U := by
  obtain ⟨h1, h2⟩ := hf
  have hQS : QlevStack (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) f = 0 := by
    refine PiLp.ext (fun p => ?_)
    rw [QlevStack_apply]
    exact h2 p.1 (Nat.lt_succ_iff.mp p.1.2) p.2.1 p.2.2
  have e2 := congrArg (fun T => T f) (desc_QlevStack h hp hell S U).e2
  simp only [ContinuousLinearMap.comp_apply, hQS, map_zero] at e2
  have hm : siteMask (S.Om 0 |> fun A => phiS h (fun _ => 0) ⁻¹' A) f = f := by
    refine PiLp.ext (fun x => ?_)
    rw [siteMask_apply]
    split_ifs with hx
    · rfl
    · exact (h1 x hx).symm
  have e3 := congrArg (fun T => T f) (desc_siteMask h (S.Om 0)).e2
  simp only [ContinuousLinearMap.comp_apply, hm] at e3
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · have : (siteMask (S.Om 0) ((covS h).sig f)) x = 0 := by
      rw [siteMask_apply]; exact if_neg hx
    rw [← e3] at this
    exact this
  · have := congrFun (congrArg WithLp.ofLp e2) ⟨⟨j, Nat.lt_succ_of_le hj⟩, ⟨y, hy⟩⟩
    exact this.symm

theorem nqp_pull [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L)
    (d : DeckIdx Lt L) (f : SiteL2 Lt) (hf : f ∈ NQp (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) :
    (covS h).pull d f ∈ NQp (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) := by
  obtain ⟨h1, h2⟩ := hf
  have hpd := phiOK_tau h hp d
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show f ((covS h).τ d x) = 0
    apply h1
    have e : ((covS h).τ d x) = phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) x := congrFun (covS_tau h d) x
    rw [e]
    intro hmem
    apply hx
    have hh := (show x ∈ (geomOf ell k (towerPull h (fun _ => 0) S)).Om0 ↔ _ from Iff.rfl)
    have : phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) x ∈ (towerPull h (fun _ => 0) S).Om 0 → x ∈ (towerPull h (fun _ => 0) S).Om 0 := by
      intro hm
      have hm' : x ∈ (towerPull (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (towerPull h (fun _ => 0) S)).Om 0 := hm
      rw [towerPull_tau h S d] at hm'
      exact hm'
    exact this hmem
  · have hnat := Qlev_nat hpd hell (towerPull h (fun _ => 0) S) (pullCfg h (fun _ => 0) U) hj f
      (y := y) (by rw [towerPull_tau h S d]; exact hy)
    rw [towerPull_tau h S d, pullCfg_tau] at hnat
    have e : (covS h).pull d f = liftF (phiS (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1))) f := by
      show liftF ((covS h).τ d) f = _
      rw [covS_tau]
    show Qlev _ _ j y ((covS h).pull d f) = 0
    rw [e, hnat]
    exact h2 j hj _ (lamHφ_tau h hp (fun d => phiOK_tau h hp d) S d ⟨j, Nat.lt_succ_of_le hj⟩ y hy)

end nqp



end AdalyFormal.Thin
