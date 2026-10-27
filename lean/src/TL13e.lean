import TL13d
import ZXR2Ops3

/-!
# TL13e -- `E₀ = L²(Ω₀ bonds)` as an abstract cover; `iE`, `pE` descend
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section e0
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem bondsOm0_tau (S : Tower L) (d : DeckIdx Lt L) (b : Bond Lt) :
    b ∈ bondsOm0 (geomOf ell k (towerPull h (fun _ => 0) S)) ↔
      phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) b ∈ bondsOm0 (geomOf ell k (towerPull h (fun _ => 0) S)) := by
  have := bondsOm0_iff (h := Covers.refl Lt) (o := fun μ => (d μ).val * (L μ + 1)) (ell := ell) (k := k)
    (S := towerPull h (fun _ => 0) S) b
  rw [towerPull_tau h S d] at this
  exact this

theorem bondSupp_ell (S : Tower L) (x : BondFnL2 L) (hx : x ∈ bondSupp (geomOf ell k S)) :
    (covE h).ell x ∈ bondSupp (geomOf ell k (towerPull h (fun _ => 0) S)) := by
  intro b hb
  show x ((covE h).π b) = 0
  rw [covE_pi]
  apply hx
  intro hmem
  exact hb ((bondsOm0_iff (h := h) (o := fun _ => 0) (ell := ell) (k := k) (S := S) b).mpr hmem)

theorem bondSupp_pull (S : Tower L) (d : DeckIdx Lt L) (y : BondFnL2 Lt)
    (hy : y ∈ bondSupp (geomOf ell k (towerPull h (fun _ => 0) S))) :
    (covE h).pull d y ∈ bondSupp (geomOf ell k (towerPull h (fun _ => 0) S)) := by
  intro b hb
  show y ((covE h).τ d b) = 0
  apply hy
  intro hmem
  apply hb
  have e : ((covE h).τ d b) = phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) b := congrFun (covE_tau h d) b
  rw [e] at hmem
  exact (bondsOm0_tau h S d b).mpr hmem

theorem bondSupp_pull_adj (S : Tower L) (d : DeckIdx Lt L) (y : BondFnL2 Lt)
    (hy : y ∈ bondSupp (geomOf ell k (towerPull h (fun _ => 0) S))) :
    ContinuousLinearMap.adjoint ((covE h).pull d : BondFnL2 Lt →L[ℝ] BondFnL2 Lt) y ∈
      bondSupp (geomOf ell k (towerPull h (fun _ => 0) S)) := by
  have e : ContinuousLinearMap.adjoint ((covE h).pull d : BondFnL2 Lt →L[ℝ] BondFnL2 Lt) = liftF (⇑((covE h).τ d).symm) :=
    adjoint_liftF_perm ((covE h).τ d)
  rw [e]
  intro b hb
  show y (((covE h).τ d).symm b) = 0
  apply hy
  intro hmem
  apply hb
  have e2 : ((covE h).τ d (((covE h).τ d).symm b)) = b := Equiv.apply_symm_apply _ _
  have e3 : ((covE h).τ d (((covE h).τ d).symm b)) = phiE (Covers.refl Lt) (fun μ => (d μ).val * (L μ + 1)) (((covE h).τ d).symm b) :=
    congrFun (covE_tau h d) _
  rw [← e2, e3]
  exact (bondsOm0_tau h S d _).mp hmem

theorem bondSupp_sig (S : Tower L) (y : BondFnL2 Lt)
    (hy : y ∈ bondSupp (geomOf ell k (towerPull h (fun _ => 0) S))) :
    (covE h).sig y ∈ bondSupp (geomOf ell k S) := by
  intro b hb
  show ∑ b' ∈ Finset.univ.filter (fun b' => (covE h).π b' = b), y b' = 0
  refine Finset.sum_eq_zero (fun b' hb' => ?_)
  have hπ := (Finset.mem_filter.mp hb').2
  rw [covE_pi] at hπ
  apply hy
  intro hmem
  apply hb
  rw [← hπ]
  exact (bondsOm0_iff (h := h) (o := fun _ => 0) (ell := ell) (k := k) (S := S) b').mp hmem

/-- `E₀ = L²(Ω₀ bonds)` as an abstract cover -/
noncomputable def hE0 (S : Tower L) :
    HCov (DeckIdx Lt L) ↥(bondSupp (geomOf ell k S)) ↥(bondSupp (geomOf ell k (towerPull h (fun _ => 0) S))) :=
  ((covE h).toH (E := SuTwo)).restrict (bondSupp (geomOf ell k S)) (bondSupp (geomOf ell k (towerPull h (fun _ => 0) S)))
    (fun x hx => bondSupp_ell h S x hx) (fun d y hy => bondSupp_pull h S d y hy)
    (fun d y hy => bondSupp_pull_adj h S d y hy)
    (fun y hy => by have := bondSupp_sig h S y hy; rwa [Cov.sig_eq_adjoint_ell] at this)

/-- the inclusion `E₀ ↪ bonds` -/
noncomputable def iE0 {L' : PeriodicLatticeExtent} (G : TowerGeom L') : ↥(bondSupp G) →L[ℝ] BondFnL2 L' := (bondSupp G).subtypeL

theorem iE0_eq {L' : PeriodicLatticeExtent} (G : TowerGeom L') : iE0 G = iE G := rfl

theorem hdesc_iE (S : Tower L) :
    HDesc (hE0 (ell := ell) (k := k) h S) ((covE h).toH (E := SuTwo)) (iE0 (geomOf ell k S))
      (iE0 (geomOf ell k (towerPull h (fun _ => 0) S))) := by
  refine ⟨?_, ?_, ?_⟩
  · ext1 x; rfl
  · unfold HE2
    ext1 y
    have hs := HCov.restrict_sig ((covE h).toH (E := SuTwo)) (bondSupp (geomOf ell k S))
      (bondSupp (geomOf ell k (towerPull h (fun _ => 0) S)))
      (fun x hx => bondSupp_ell h S x hx) (fun d y hy => bondSupp_pull h S d y hy)
      (fun d y hy => bondSupp_pull_adj h S d y hy)
      (fun y hy => by have := bondSupp_sig h S y hy; rwa [Cov.sig_eq_adjoint_ell] at this)
    simp only [ContinuousLinearMap.comp_apply]
    show _ = ((hE0 (ell := ell) (k := k) h S).sig y).1
    unfold hE0
    rw [hs]
    rfl
  · intro d
    ext1 x
    rfl

end e0



end AdalyFormal.Thin
