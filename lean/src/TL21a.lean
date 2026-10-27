import TL20c

/-!
# TL21a -- `genForm` lifts: `genForm(Pt)(ℓ B) = N · genForm(P)(B)`
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
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

section gf
variable {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell k : ℕ} (hell : 0 < ell)
variable (S : Tower (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

/-- the hypotheses AT THE COVER under which the genuine operators descend (units of every inverse in the definition of `genForm`,
`C²`-regularity of the aligned averaging rows, bijectivity of `H₀`) -/
structure CoverHyp (hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)) : Prop where
  hT1 : ∀ μ : Fin 3, ell ∣ Lu μ + 1
  hreg : JetReg ell k (towerPull (covers_scaleUp ell k hell hu) (fun _ => 0) S) (UbarTower su2LogExp ell (pullCfg (covers_scaleUp ell k hell hu) (fun _ => 0) U))
  ureg : UnitReg hu hell S U a Lam
  gp : IsUnit (DelpA (geomOf ell k (towerPull (covers_scaleUp ell k hell hu) (fun _ => 0) S))
    (pullCfg (covers_scaleUp ell k hell hu) (fun _ => 0) U) a +
    (1 - siteMask (geomOf ell k (towerPull (covers_scaleUp ell k hell hu) (fun _ => 0) S)).Om0))
  ginv : IsUnit (Pt hu hell S U a Lam).data.Ginv
  qgqs : IsUnit (((Pt hu hell S U a Lam).data.Q.comp (Pt hu hell S U a Lam).data.G).comp (Pt hu hell S U a Lam).data.Qs)
  g1inv : IsUnit (Pt hu hell S U a Lam).G1inv
  nmat : IsUnit (GenP.Nmat (Pt hu hell S U a Lam))
  h0 : Function.Bijective (H0 (Pt hu hell S U a Lam).Lam (Pt hu hell S U a Lam).Q1)

variable {hu hell S U a Lam}

theorem CoverHyp.bd [Nonempty (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu))]
    {hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)} (hc : CoverHyp hu hell S U a Lam hp) :
    BDLink (Dd := DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) (P0 hell S U a Lam).data (Pt hu hell S U a Lam).data
      (hE0 (ell := ell) (k := k) (covers_scaleUp ell k hell hu) S) (cSite (covers_scaleUp ell k hell hu))
      (cFSp (covers_scaleUp ell k hell hu) hp hell S) :=
  bdlink_base (covers_scaleUp ell k hell hu) hp hell S U a hc.hreg hc.gp

theorem genForm_lift [Nonempty (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu))]
    {hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)} (hc : CoverHyp hu hell S U a Lam hp) (B : BondFnL2 Lu) :
    GenP.genForm (Pt hu hell S U a Lam) (liftF (phiE hu (fun _ => 0)) B) =
      (Fintype.card (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) : ℝ) * GenP.genForm (P0 hell S U a Lam) B := by
  have hf := covers_scaleUp ell k hell hu
  have bd := hc.bd
  have hH := bd.H hc.ginv hc.qgqs
  have hG1d := bd.G1inv hH (P0 hell S U a Lam).G1inv_spec (Pt hu hell S U a Lam).G1inv_spec
  have hNd := bd.Nmat hG1d hc.g1inv
  have hNinv := (hNd.inverse hc.nmat).2
  have hH1 := bd.H1 hG1d hc.g1inv hc.nmat
  have htau := (desc_tau hu ell k hell hp S).toH
  have hτa := htau.adjoint
  set cU : HCov (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) (BondFnL2 Lu) (BondFnL2 Lut) :=
    (covEU hu ell k hell).toH (E := SuTwo) with hcU
  set cB' : HCov (DeckIdx (scaleUp ell k Lut) (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lut)) :=
    cB hf with hcB
  have hX : liftF (phiE hu (fun _ => 0)) B = cU.ell B := by
    rw [hcU]; show _ = liftF (covEU hu ell k hell).π B; rw [covEU_pi]
  -- T1
  have T1 : ContinuousLinearMap.adjoint (Pt hu hell S U a Lam).tau (cU.ell B) =
      (cFSp hf hp hell S).ell (ContinuousLinearMap.adjoint (P0 hell S U a Lam).tau B) :=
    congrArg (fun T => T B) hτa.e1
  -- T2
  have T2 : ∀ w, Ring.inverse (GenP.Nmat (Pt hu hell S U a Lam)) ((cFSp hf hp hell S).ell w) =
      (cFSp hf hp hell S).ell (Ring.inverse (GenP.Nmat (P0 hell S U a Lam)) w) :=
    fun w => congrArg (fun T => T w) hNinv.e1
  -- T6
  have hH1in : HDesc cU cB' (P0 hell S U a Lam).H1in (Pt hu hell S U a Lam).H1in :=
    (hτa.comp hH1).comp (hdesc_iE (ell := ell) (k := k) hf S)
  have T6 : (Pt hu hell S U a Lam).H1in (cU.ell ((P0 hell S U a Lam).D2in B)) = cB'.ell ((P0 hell S U a Lam).H1in ((P0 hell S U a Lam).D2in B)) :=
    congrArg (fun T => T ((P0 hell S U a Lam).D2in B)) hH1in.e1
  have T5 : (Pt hu hell S U a Lam).D2in (cU.ell B) = cU.ell ((P0 hell S U a Lam).D2in B) := by
    rw [← hX]; exact D2in_nat hu hell S U a Lam hc.hT1 hp hc.ureg hc.h0 B
  have T7 : (Pt hu hell S U a Lam).Jf = cB'.ell (P0 hell S U a Lam).Jf := by
    show JfG _ _ = _
    rw [JfG_nat hf S U]
    show _ = liftF (covE hf).π _
    rw [covE_pi]
    rfl
  rw [hX]
  unfold GenP.genForm GenP.firstTerm
  have he : (Pt hu hell S U a Lam).eta = (P0 hell S U a Lam).eta := rfl
  have ha : (Pt hu hell S U a Lam).a = (P0 hell S U a Lam).a := rfl
  rw [T1, T2, T5, T6, T7, HCov.inner_ell, HCov.inner_ell, HCov.inner_ell, he, ha]
  ring

end gf


end AdalyFormal.Thin
