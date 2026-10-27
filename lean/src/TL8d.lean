import TL8c

/-!
# TL8d -- the index covers of `L²(Λ_j)` and `L²(𝔅)`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

section idx
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ} (S : Tower L)

/-- `⨆_j Λ_j` as a sigma type of sites -/
abbrev LamIdx (G : TowerGeom L) : Type := Σ j : Fin (G.k + 1), {y : PeriodicLatticeSite L // y ∈ G.Lam j}

open Classical in
noncomputable instance (G : TowerGeom L) : Fintype (LamIdx G) := inferInstance

theorem projS_zero (x : PeriodicLatticeSite Lt) : projS h x = phiS h (fun _ => 0) x := congrFun (projS_eq_phiS h) x

open Classical in
/-- cover of `⨆_j Λ_j` (tilde tower = pulled back tower) -/
noncomputable def covLamIdx (hp : PhiOK h (fun _ => 0) (ell ^ k)) :
    Cov (DeckIdx Lt L) (LamIdx (geomOf ell k (towerPull h (fun _ => 0) S))) (LamIdx (geomOf ell k S)) :=
  Cov.sigma (fun j : Fin (k + 1) =>
    ((covS h).sub (fun y => y ∈ (geomOf ell k S).Lam j)).transport
      (Equiv.subtypeEquivRight (fun x => by
        have := lam_iff (S := S) hp (Nat.lt_succ_iff.mp j.2) x
        rw [covS_pi h]
        exact this)))

open Classical in
/-- cover of `𝔅` -/
noncomputable def covBIdx (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) :
    Cov (DeckIdx Lt L) (BIdx (geomOf ell k (towerPull h (fun _ => 0) S))) (BIdx (geomOf ell k S)) :=
  Cov.sigma (fun j : Fin (k + 1) =>
    ((covE h).sub (fun b => b ∈ bondsLam (geomOf ell k S) j)).transport
      (Equiv.subtypeEquivRight (fun b => by
        have := bondsLam_iff (S := S) hp hell (Nat.lt_succ_iff.mp j.2) b
        rw [covE_pi h]
        exact this)))

end idx

end AdalyFormal.Thin
