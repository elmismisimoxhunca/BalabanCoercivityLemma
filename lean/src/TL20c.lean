import TL20b

/-!
# TL20c -- `C` and `D̃⁽²⁾` of the genuine family are natural
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp SU2)
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)
open AdalyFormal.IngredientFamilyR2

section unitlv2
variable {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell k : ℕ} (hell : 0 < ell)
variable (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

theorem dmap_surj (hT1 : ∀ μ : Fin 3, ell ∣ Lu μ + 1) :
    Function.Surjective (dmap (hu := hu) (o := fun _ => 0) (ell := ell) ⟨hT1, fun _ => dvd_zero _⟩ hell Lam) := by
  have hp : PhiOK hu (fun _ => 0) ell := ⟨hT1, fun _ => dvd_zero _⟩
  intro c
  obtain ⟨y, hy⟩ := projS_surj hu c.1.1.1
  have hy' : phiS hu (fun _ => 0) y = c.1.1.1 := by rw [← projS_zero hu y]; exact hy
  have hal : Aligned ell y := (aligned_phiS hp y).mp (by rw [hy']; exact coarse_aligned _ c.1.1.2)
  have hyc : y ∈ CoarseLattice Lut ell := mem_CoarseLattice.mpr (fun ν => Nat.mod_eq_zero_of_dvd (hal ν))
  have hcb : cbMap hp ((⟨y, hyc⟩ : { y : PeriodicLatticeSite Lut // y ∈ CoarseLattice Lut ell }), c.1.2) = c.1 := by
    unfold cbMap
    exact Prod.ext (Subtype.ext hy') rfl
  refine ⟨⟨(⟨y, hyc⟩, c.1.2), (CRowIn_pull hp hell Lam _).mpr (by rw [hcb]; exact c.2)⟩, ?_⟩
  exact Subtype.ext hcb

theorem genC_nat (hT1 : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (hpk : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k))
    (hreg : UnitReg hu hell S U a Lam)
    (hbt : Function.Bijective (H0 (phiS hu (fun _ => 0) ⁻¹' Lam) (Pt hu hell S U a Lam).Q1)) (B : Bond Lu → SuTwo) :
    GenP.genC (Pt hu hell S U a Lam) (fun e => B (phiE hu (fun _ => 0) e)) =
      fun b => GenP.genC (P0 hell S U a Lam) B (phiE hu (fun _ => 0) b) :=
  Cop_nat ⟨hT1, fun _ => dvd_zero _⟩ hell Lam (Pt hu hell S U a Lam).Q1 (P0 hell S U a Lam).Q1
    (fun B c hc => Q1_nat hu hell S U a Lam hT1 hpk hreg B c hc) (dmap_surj hu hell Lam hT1) hbt B

theorem D2in_nat (hT1 : ∀ μ : Fin 3, ell ∣ Lu μ + 1) (hpk : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k))
    (hreg : UnitReg hu hell S U a Lam)
    (hbt : Function.Bijective (H0 (phiS hu (fun _ => 0) ⁻¹' Lam) (Pt hu hell S U a Lam).Q1)) (B : BondFnL2 Lu) :
    (Pt hu hell S U a Lam).D2in (liftF (phiE hu (fun _ => 0)) B) = liftF (phiE hu (fun _ => 0)) ((P0 hell S U a Lam).D2in B) := by
  have hp : PhiOK hu (fun _ => 0) ell := ⟨hT1, fun _ => dvd_zero _⟩
  have hU := unitBgU_nat hu hell S U a Lam hpk
  have hC2 : ∀ c : CoarseBond Lut ell, CRowIn ell (phiS hu (fun _ => 0) ⁻¹' Lam) c →
      C2tilde ell (Pt hu hell S U a Lam).unitBgU (fun e => (WithLp.ofLp B) (phiE hu (fun _ => 0) e)) c =
        C2tilde ell (P0 hell S U a Lam).unitBgU (WithLp.ofLp B) (cbMap hp c) := fun c hc =>
    C2tilde_nat hp hell (fun e _ => by rw [hU]) (WithLp.ofLp B) c (hreg c hc)
  refine PiLp.ext (fun b => ?_)
  show ((ell : ℝ)⁻¹) • (hLift (phiS hu (fun _ => 0) ⁻¹' Lam) (Pt hu hell S U a Lam).Q1
      (C2tilde ell (Pt hu hell S U a Lam).unitBgU (fun e => (WithLp.ofLp B) (phiE hu (fun _ => 0) e)))) b =
    ((ell : ℝ)⁻¹) • (hLift Lam (P0 hell S U a Lam).Q1 (C2tilde ell (P0 hell S U a Lam).unitBgU (WithLp.ofLp B))) (phiE hu (fun _ => 0) b)
  rw [hLift_congr_rows _ _ hC2, hLift_nat hp hell Lam (Pt hu hell S U a Lam).Q1 (P0 hell S U a Lam).Q1
    (fun B c hc => Q1_nat hu hell S U a Lam hT1 hpk hreg B c hc) (dmap_surj hu hell Lam hT1) hbt]

end unitlv2


end AdalyFormal.Thin
