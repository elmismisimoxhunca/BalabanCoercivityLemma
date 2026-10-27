import TL18a

/-!
# TL18b -- `H₀`, `H₀⁻¹`, `h`, `C` natural
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

theorem hLift_congr_rows {L : PeriodicLatticeExtent} {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (CoarseBond L ell → SuTwo)) {f g : CoarseBond L ell → SuTwo}
    (h : ∀ c, CRowIn ell Lam c → f c = g c) : hLift Lam Q f = hLift Lam Q g := by
  have hr : rhoD ell Lam f = rhoD ell Lam g := funext (fun c => h c.1 c.2)
  show iotaD _ _ (H0inv _ Q (rhoD _ _ f)) = iotaD _ _ (H0inv _ Q (rhoD _ _ g))
  rw [hr]

section u3
variable {Lut Lu : PeriodicLatticeExtent} {hu : Covers Lut Lu} {o : Fin 3 → ℕ} {ell : ℕ}
variable (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu))
variable (Qt : (Bond Lut → SuTwo) →ₗ[ℝ] (CoarseBond Lut ell → SuTwo)) (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo))

theorem H0_nat (hQ : ∀ B : Bond Lu → SuTwo, ∀ c : CoarseBond Lut ell, CRowIn ell (phiS hu o ⁻¹' Lam) c →
      Qt (fun e => B (phiE hu o e)) c = Q B (cbMap hp c))
    (w : Dset Lu ell Lam → SuTwo) :
    H0 (phiS hu o ⁻¹' Lam) Qt (fun c => w (dmap hp hell Lam c)) = fun c => H0 Lam Q w (dmap hp hell Lam c) := by
  funext c
  show Qt (iotaD ell (phiS hu o ⁻¹' Lam) (fun c => w (dmap hp hell Lam c))) c.1 = Q (iotaD ell Lam w) (cbMap hp c.1)
  rw [iotaD_nat hp hell Lam w]
  exact hQ (iotaD ell Lam w) c.1 c.2

theorem H0inv_nat (hQ : ∀ B : Bond Lu → SuTwo, ∀ c : CoarseBond Lut ell, CRowIn ell (phiS hu o ⁻¹' Lam) c →
      Qt (fun e => B (phiE hu o e)) c = Q B (cbMap hp c))
    (hsurj : Function.Surjective (dmap hp hell Lam)) (hbt : Function.Bijective (H0 (phiS hu o ⁻¹' Lam) Qt))
    (w : Dset Lu ell Lam → SuTwo) :
    Function.Bijective (H0 Lam Q) ∧
    H0inv (phiS hu o ⁻¹' Lam) Qt (fun c => w (dmap hp hell Lam c)) = fun c => H0inv Lam Q w (dmap hp hell Lam c) := by
  have hinj : Function.Injective (H0 Lam Q) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : H0 (phiS hu o ⁻¹' Lam) Qt (fun c => v (dmap hp hell Lam c)) = 0 := by
      rw [H0_nat hp hell Lam Qt Q hQ, hv]; rfl
    have h2 : (fun c => v (dmap hp hell Lam c)) = 0 := (injective_iff_map_eq_zero _).mp hbt.1 _ h1
    funext d
    obtain ⟨c, rfl⟩ := hsurj d
    exact congrFun h2 c
  have hbij : Function.Bijective (H0 Lam Q) :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := H0 Lam Q)).mp hinj⟩
  refine ⟨hbij, ?_⟩
  apply hbt.1
  rw [H0_H0inv _ Qt hbt]
  rw [H0_nat hp hell Lam Qt Q hQ, H0_H0inv Lam Q hbij]

theorem hLift_nat (hQ : ∀ B : Bond Lu → SuTwo, ∀ c : CoarseBond Lut ell, CRowIn ell (phiS hu o ⁻¹' Lam) c →
      Qt (fun e => B (phiE hu o e)) c = Q B (cbMap hp c))
    (hsurj : Function.Surjective (dmap hp hell Lam)) (hbt : Function.Bijective (H0 (phiS hu o ⁻¹' Lam) Qt))
    (f : CoarseBond Lu ell → SuTwo) :
    hLift (phiS hu o ⁻¹' Lam) Qt (fun c => f (cbMap hp c)) = fun b => hLift Lam Q f (phiE hu o b) := by
  show iotaD ell (phiS hu o ⁻¹' Lam) (H0inv (phiS hu o ⁻¹' Lam) Qt (rhoD ell (phiS hu o ⁻¹' Lam) (fun c => f (cbMap hp c)))) =
    fun b => iotaD ell Lam (H0inv Lam Q (rhoD ell Lam f)) (phiE hu o b)
  rw [rhoD_nat hp hell Lam f, (H0inv_nat hp hell Lam Qt Q hQ hsurj hbt _).2, iotaD_nat hp hell Lam]

theorem Cop_nat (hQ : ∀ B : Bond Lu → SuTwo, ∀ c : CoarseBond Lut ell, CRowIn ell (phiS hu o ⁻¹' Lam) c →
      Qt (fun e => B (phiE hu o e)) c = Q B (cbMap hp c))
    (hsurj : Function.Surjective (dmap hp hell Lam)) (hbt : Function.Bijective (H0 (phiS hu o ⁻¹' Lam) Qt))
    (B : Bond Lu → SuTwo) :
    Cop (phiS hu o ⁻¹' Lam) Qt (fun e => B (phiE hu o e)) = fun b => Cop Lam Q B (phiE hu o b) := by
  show (fun e => B (phiE hu o e)) - hLift (phiS hu o ⁻¹' Lam) Qt (Qt (fun e => B (phiE hu o e))) =
    fun b => (B - hLift Lam Q (Q B)) (phiE hu o b)
  have hL : hLift (phiS hu o ⁻¹' Lam) Qt (Qt (fun e => B (phiE hu o e))) =
      hLift (phiS hu o ⁻¹' Lam) Qt (fun c => Q B (cbMap hp c)) :=
    hLift_congr_rows _ Qt (fun c hc => hQ B c hc)
  rw [hL, hLift_nat hp hell Lam Qt Q hQ hsurj hbt]
  rfl

end u3

end AdalyFormal.Thin
