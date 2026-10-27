import TL21a

/-!
# TL21b -- `InstIneq` descends from the cover
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem liftU_eq {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (U : LinkCfg L) :
    liftU h U = pullCfg h (fun _ => 0) U := by
  funext e
  show U (projE h e) = U (phiE h (fun _ => 0) e)
  have : projE h e = phiE h (fun _ => 0) e := by
    simp only [projE, phiE, projS_eq_phiS]
  rw [this]

theorem card_deck_scaleUp {Lut Lu : PeriodicLatticeExtent} (ell k : ℕ) (hell : 0 < ell) :
    Fintype.card (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) = Fintype.card (DeckIdx Lut Lu) :=
  Fintype.card_congr (eUnit ell k hell)

section ii
variable {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell k : ℕ} (hell : 0 < ell)
variable (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

theorem instIneq_of_lift {hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)}
    (hc : CoverHyp hu hell S U a Lam hp) {γ₀ : ℝ} (hγ : 0 ≤ γ₀)
    (hI : InstIneq ell k hell a Lut γ₀ (towerPull (covers_scaleUp ell k hell hu) (fun _ => 0) S)
      (phiS hu (fun _ => 0) ⁻¹' Lam) (pullCfg (covers_scaleUp ell k hell hu) (fun _ => 0) U)) :
    InstIneq ell k hell a Lu γ₀ S Lam U := by
  haveI := deckIdx_nonempty (covers_scaleUp ell k hell hu)
  have hpOK : PhiOK hu (fun _ => 0) ell := ⟨hc.hT1, fun _ => dvd_zero _⟩
  intro Bt h1 h2
  have h := hI (fun e => Bt (phiE hu (fun _ => 0) e)) (onLambdaTildeIn_pull hpOK hell Lam Bt h1)
    (onLambdaT_pull Lam Bt h2)
  have hC := genC_nat hu hell S U a Lam hc.hT1 hp hc.ureg hc.h0 Bt
  have hG : (WithLp.toLp 2 (GenP.genC (Pt hu hell S U a Lam) (fun e => Bt (phiE hu (fun _ => 0) e))) : BondFnL2 Lut) =
      liftF (phiE hu (fun _ => 0)) (WithLp.toLp 2 (GenP.genC (P0 hell S U a Lam) Bt)) := by
    rw [hC]; rfl
  have hgf := genForm_lift hc (WithLp.toLp 2 (GenP.genC (P0 hell S U a Lam) Bt))
  have hE := bondEnergy_pull (hu := hu) Bt
  have hN : (0 : ℝ) < (Fintype.card (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hN' : Fintype.card (DeckIdx Lut Lu) = Fintype.card (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) :=
    (card_deck_scaleUp ell k hell).symm
  change γ₀ * bondEnergy (fun e => Bt (phiE hu (fun _ => 0) e)) ≤
    GenP.genForm (Pt hu hell S U a Lam) (WithLp.toLp 2 (GenP.genC (Pt hu hell S U a Lam) (fun e => Bt (phiE hu (fun _ => 0) e)))) at h
  rw [hG, hgf, hE, hN'] at h
  nlinarith

end ii

end AdalyFormal.Thin

#print axioms AdalyFormal.Thin.instIneq_of_lift
#print axioms AdalyFormal.Thin.genForm_lift
