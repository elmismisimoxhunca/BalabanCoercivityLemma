import TL17c

/-!
# TL18a -- `C̃⁽²⁾`, the dropped-bond lift `ι_D`, `ρ`, `H₀`, `H₀⁻¹`, `h`, `C` are natural (function level)
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
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.IngredientFamilyR2

section u2
variable {Lut Lu : PeriodicLatticeExtent} {hu : Covers Lut Lu} {o : Fin 3 → ℕ} {ell : ℕ}

theorem C2tilde_nat (hp : PhiOK hu o ell) (hell : 0 < ell)
    {V0t : PeriodicLinkConfiguration SU2 Lut} {V0 : PeriodicLinkConfiguration SU2 Lu} (h0 : AgreeAligned hu o 1 V0t V0)
    (B : Bond Lu → SuTwo) (c : CoarseBond Lut ell)
    (hC2 : ContDiffAt ℝ 2 (qStepComp 1 ell V0t (c.1.1, c.2)) 0) :
    C2tilde ell V0t (fun e => B (phiE hu o e)) c = C2tilde ell V0 B (cbMap hp c) := by
  have hp1 : PhiOK hu o (1 * ell) := by simpa using hp
  show (suCoordFInv (C2StepL 1 ell V0t (suCoordF (fun e => B (phiE hu o e))))) (c.1.1, c.2) =
    (suCoordFInv (C2StepL 1 ell V0 (suCoordF B))) ((cbMap hp c).1.1, (cbMap hp c).2)
  have hrow := D2StepL_row_nat hp1 Nat.one_pos hell h0 (c := (c.1.1, c.2)) (by simpa using coarse_aligned c.1.1 c.1.2)
    hC2 (suCoordF (fun e => B (phiE hu o e))) (suCoordF (fun e => B (phiE hu o e))) (suCoordF B) (suCoordF B)
    (fun e _ => rfl) (fun e _ => rfl)
  apply Subtype.ext
  show toM2 _ = toM2 _
  show toM2 (((1 / 2 : ℝ) • D2StepL 1 ell V0t _ _) (c.1.1, c.2)) = toM2 (((1 / 2 : ℝ) • D2StepL 1 ell V0 _ _) (phiE hu o (c.1.1, c.2)))
  simp only [Pi.smul_apply]
  rw [hrow]

theorem dropped_injective {L' : PeriodicLatticeExtent} (ell : ℕ) : Function.Injective (droppedBondLast (L := L') ell) := by
  intro c c' h
  have h1 : (pathSite c.1.1 c.2 (ell - 1), c.2) = (pathSite c'.1.1 c'.2 (ell - 1), c'.2) := h
  obtain ⟨hy, hμ⟩ := Prod.mk.inj h1
  rw [← hμ] at hy
  have := congrArg (fun z => (fun z' => AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack z' c.2)^[ell - 1] z) hy
  simp only [sbIter_pathSite] at this
  exact Prod.ext (Subtype.ext this) hμ

/-- the induced map on the dropped-bond index set -/
def dmap (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (c : Dset Lut ell (phiS hu o ⁻¹' Lam)) :
    Dset Lu ell Lam := ⟨cbMap hp c.1, (CRowIn_pull hp hell Lam c.1).mp c.2⟩

theorem iotaD_nat (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (w : Dset Lu ell Lam → SuTwo) :
    iotaD ell (phiS hu o ⁻¹' Lam) (fun c => w (dmap hp hell Lam c)) = fun b => iotaD ell Lam w (phiE hu o b) := by
  funext b
  by_cases hd : IsDroppedIn (phiS hu o ⁻¹' Lam) ell b
  · obtain ⟨c, hc, rfl⟩ := hd
    rw [iotaD_apply_dropped (phiS hu o ⁻¹' Lam) (dropped_injective ell) _ ⟨c, hc⟩, dropped_nat hp]
    have := iotaD_apply_dropped Lam (dropped_injective ell) w (dmap hp hell Lam ⟨c, hc⟩)
    exact this.symm
  · rw [iotaD_apply_not_dropped _ _ b hd, iotaD_apply_not_dropped Lam w (phiE hu o b)]
    rw [isDropped_pull hp hell Lam b] at hd
    exact hd

theorem rhoD_nat (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (f : CoarseBond Lu ell → SuTwo) :
    rhoD ell (phiS hu o ⁻¹' Lam) (fun c => f (cbMap hp c)) = fun c => rhoD ell Lam f (dmap hp hell Lam c) := rfl

end u2

end AdalyFormal.Thin
