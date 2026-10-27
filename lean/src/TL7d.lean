import TL7c
import AdalyFormal.Balaban.UbarTowerCovariance

/-!
# TL7d -- the background tower `Ū^l` is natural at aligned bonds
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf inStepBlock)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar UbarTower cPlusS_eq)

section ubar
variable {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}
abbrev SU2c := Matrix.specialUnitaryGroup (Fin 2) ℂ

theorem cPlusS_nat (h : Covers Lt L) (o : Fin 3 → ℕ) (s ell : ℕ) (c : PeriodicLatticeEdge Lt) :
    phiS h o (cPlusS s ell c) = cPlusS s ell (phiE h o c) := by
  rw [cPlusS_eq, cPlusS_eq, coarseShift_nat]
  rfl

theorem aligned_cPlusS {L' : PeriodicLatticeExtent} (hs : ∀ μ, s * ell ∣ L' μ + 1) {c : PeriodicLatticeEdge L'}
    (hc : Aligned (s * ell) c.1) : Aligned (s * ell) (cPlusS s ell c) := by
  rw [cPlusS_eq]
  exact aligned_coarseShift hs hc c.2

theorem coarseBondVar_nat (hp : PhiOK h o s) {Vt : PeriodicLinkConfiguration SU2c Lt} {V : PeriodicLinkConfiguration SU2c L}
    (hV : AgreeAligned h o s Vt V) {c : PeriodicLatticeEdge Lt} (hc : Aligned s c.1) :
    coarseBondVar s ell Vt c = coarseBondVar s ell V (phiE h o c) := by
  unfold coarseBondVar
  exact coarsePathHolonomy_nat hp hV _ _ hc

theorem gammaVarStrided_nat (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {Vt : PeriodicLinkConfiguration SU2c Lt} {V : PeriodicLinkConfiguration SU2c L}
    (hV : AgreeAligned h o s Vt V) {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1)
    {x : PeriodicLatticeSite Lt} (hx : x ∈ stepBlockOf c.1 s ell) :
    gammaVarStrided s ell Vt c x = gammaVarStrided s ell V (phiE h o c) (phiS h o x) := by
  have hps : PhiOK h o s := hp.mono (Dvd.intro ell rfl)
  have hcs : Aligned s c.1 := aligned_of_mul hc
  have hxs : Aligned s x := aligned_of_block hcs hx
  have hcp : Aligned s (cPlusS s ell c) := aligned_of_mul (aligned_cPlusS (fun μ => (hp.side μ).trans (h μ)) hc)
  unfold gammaVarStrided
  rw [coarsePathHolonomy_nat hps hV _ _ hcs, coarsePathHolonomy_nat hps hV _ _ hxs,
    coarsePathHolonomy_nat hps hV _ _ hcp, cPlusS_nat, ← coarseGammaPath_nat hp hs hell hc hx]
  rfl

theorem loopVar_nat (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {Vt : PeriodicLinkConfiguration SU2c Lt} {V : PeriodicLinkConfiguration SU2c L}
    (hV : AgreeAligned h o s Vt V) {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1)
    {x : PeriodicLatticeSite Lt} (hx : x ∈ stepBlockOf c.1 s ell) :
    loopVar s ell Vt c x = loopVar s ell V (phiE h o c) (phiS h o x) := by
  unfold loopVar
  rw [gammaVarStrided_nat hp hs hell hV hc hx, coarseBondVar_nat (hp.mono (Dvd.intro ell rfl)) hV (aligned_of_mul hc)]

theorem stridedBlockedGauge_nat {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℚ 𝔤] (P : AdalyFormal.Balaban.BlockedGauge.LogExpAd SU2c 𝔤)
    (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {Vt : PeriodicLinkConfiguration SU2c Lt} {V : PeriodicLinkConfiguration SU2c L}
    (hV : AgreeAligned h o s Vt V) {c : PeriodicLatticeEdge Lt} (hc : Aligned (s * ell) c.1) :
    stridedBlockedGauge P s ell Vt c = stridedBlockedGauge P s ell V (phiE h o c) := by
  unfold stridedBlockedGauge
  congr 1
  · congr 1
    show _ = ∑ x ∈ stepBlockOf (phiS h o c.1) s ell, ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V (phiE h o c) x)
    rw [← stepBlock_sum hp hs hell hc (fun x => ((ell : ℚ) ^ 3)⁻¹ • P.log (loopVar s ell V (phiE h o c) x))]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [loopVar_nat hp hs hell hV hc hx]
  · exact coarseBondVar_nat (hp.mono (Dvd.intro ell rfl)) hV (aligned_of_mul hc)

theorem UbarTower_nat {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℚ 𝔤] (P : AdalyFormal.Balaban.BlockedGauge.LogExpAd SU2c 𝔤)
    (hell : 0 < ell) (U : PeriodicLinkConfiguration SU2c L) :
    ∀ l : ℕ, PhiOK h o (ell ^ l) →
      AgreeAligned h o (ell ^ l) (UbarTower P ell (fun e => U (phiE h o e)) l) (UbarTower P ell U l) := by
  intro l
  induction l with
  | zero =>
    intro _ e _
    rfl
  | succ l ih =>
    intro hp e he
    have hpos : 0 < ell ^ l := pow_pos hell l
    have hp' : PhiOK h o (ell ^ l * ell) := by rw [← pow_succ]; exact hp
    have he' : Aligned (ell ^ l * ell) e.1 := by rw [← pow_succ]; exact he
    exact stridedBlockedGauge_nat P hp' hpos hell (ih (hp.mono (pow_dvd_pow ell (Nat.le_succ l)))) he'

end ubar

end AdalyFormal.Thin
