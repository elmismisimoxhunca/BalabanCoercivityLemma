import DK2DepthFittedOffsets

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedRepair

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp su2LogExp_exp su2LogExp_log)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)
open AdalyFormal.Balaban.UbarTowerCov
  (gammaVarStrided coarseBondVar cPlusS_eq stridedBlockedGauge loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open DepthUniformity.Strided (orientedPlaqHolS)
open SmallnessBridge.Assemble (coarseShift_comm)

variable {L : PeriodicLatticeExtent}

/-- Exact contour evaluated at a common offset, using the original staircase. -/
theorem gamma_at_offset (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (s*ell))
    (o : Fin 3 → Fin ell) :
    gammaVarStrided s ell V c (offsetPoint s c.1 o) =
      coarsePathHolonomy s V c.1 (offsetPath o) *
        coarseBondVar s ell V (offsetPoint s c.1 o, c.2) *
        (coarsePathHolonomy s V (coarseShift c.1 (s*ell) c.2) (offsetPath o))⁻¹ := by
  unfold gammaVarStrided
  rw [offsetPoint_path s ell hs hd c.1 hc o, cPlusS_eq]
  rfl

/-- Exact common-offset contour cancellation on the periodic lattice, including
wraparound. The entire rectangle, not any of its open sides, is conjugated. -/
theorem gamma_offset_rectangle (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s*ell))
    (μ ν : Fin 3) (o : Fin 3 → Fin ell) :
    orientedPlaqHolS (s*ell)
      (fun c => gammaVarStrided s ell V c (offsetPoint s c.1 o)) y μ ν =
    coarsePathHolonomy s V y (offsetPath o) *
      orientedPlaqHolS (s*ell) (coarseBondVar s ell V) (offsetPoint s y o) μ ν *
      (coarsePathHolonomy s V y (offsetPath o))⁻¹ := by
  have hμ := coarseShift_mem_coarseLattice hd hy μ
  have hν := coarseShift_mem_coarseLattice hd hy ν
  unfold orientedPlaqHolS
  dsimp only
  rw [gamma_at_offset s ell hs hd V (y, μ) hy o,
    gamma_at_offset s ell hs hd V (coarseShift y (s*ell) μ, ν) hμ o,
    gamma_at_offset s ell hs hd V (coarseShift y (s*ell) ν, μ) hν o,
    gamma_at_offset s ell hs hd V (y, ν) hy o]
  simp only [offsetPoint_shift]
  rw [coarseShift_comm y (s*ell) (s*ell) μ ν]
  exact contour_rectangle_cancellation _ _ _ _ _ _ _ _

/-- Exact raw averaging formula reindexed into a common offset set. -/
theorem raw_bond_offset_mean (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1) (V : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (s*ell)) :
    ubarSU2 s ell V c =
      loopMean Finset.univ (fun _ : Fin 3 → Fin ell => ((((ell : ℚ)^3)⁻¹ : ℚ) : ℝ))
        (fun o => gammaVarStrided s ell V c (offsetPoint s c.1 o) *
          (coarseBondVar s ell V c)⁻¹) * coarseBondVar s ell V c := by
  unfold ubarSU2 stridedBlockedGauge loopMean
  rw [sum_block_offsets s ell hs hd c.1 hc]
  simp only [su2LogExp_exp, su2LogExp_log, Rat.cast_smul_eq_qsmul, loopVar]

end Prop1.ScaleFittedRepair

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedRepair.gamma_at_offset,
      `Prop1.ScaleFittedRepair.gamma_offset_rectangle,
      `Prop1.ScaleFittedRepair.raw_bond_offset_mean] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"OFFSET_CONTOUR_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "OFFSET_CONTOURS_COMPLETE"
