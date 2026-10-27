import DK2DepthTransportMean

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedRepair

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite
  (coarsePathEndpoint_cons coarsePathEndpoint_replicate stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar coarseBondVar)
open AdalyFormal.Balaban.BlockingLinkEstimate
  (frobNorm_conj_sub_one frobNorm_prod_sub_one_le)
open SmallnessBridge.Assemble
  (holonomyFactors holonomyFactors_prod holonomyFactors_nil conjBy loopSurfaceBound)
open DepthUniformity.Strided
open DepthUniformity.Fitted (SublatticePlaqBound coarseLattice_antitone)

variable {L : PeriodicLatticeExtent}

theorem path_endpoint_aligned (s : ℕ) (hd : ∀ μ : Fin 3, s ∣ L μ + 1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (p : List (Fin 3)) :
    coarsePathEndpoint s y p ∈ CoarseLattice L s := by
  induction p generalizing y with
  | nil => exact hy
  | cons μ p ih =>
      rw [coarsePathEndpoint_cons]
      exact ih _ (coarseShift_mem_coarseLattice hd hy μ)

/-- Surface rungs use only input-aligned plaquettes. The existing global-angle
interface is deliberately not used: its hypotheses are stronger than the target. -/
theorem fitted_ladder_factor_bound (s : ℕ) (hd : ∀ μ : Fin 3, s ∣ L μ + 1)
    (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) (hin : SublatticePlaqBound s V β)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s)
    (μ ν : Fin 3) (ell : ℕ) {g : SU2} (hg : g ∈ ladderFactorsS s V y μ ν ell) :
    frobNorm ((g : M2)-1) ≤ β := by
  induction ell generalizing y with
  | zero => simp [ladderFactorsS] at hg
  | succ n ih =>
      unfold ladderFactorsS at hg
      split_ifs at hg with hμν
      · simp at hg
      · simp only [List.mem_cons] at hg
        rcases hg with hg | hg
        · subst g
          have hconj (a b : SU2) : frobNorm (((a⁻¹*b*a : SU2) : M2)-1) =
              frobNorm ((b : M2)-1) := by
            simpa only [inv_inv] using frobNorm_conj_sub_one a⁻¹ b
          rw [hconj, hconj, frobNorm_inv_sub_one]
          exact hin y hy μ ν
        · exact ih _ (coarseShift_mem_coarseLattice hd hy μ) hg

theorem fitted_surface_factor_bound (s : ℕ) (hd : ∀ μ : Fin 3, s ∣ L μ + 1)
    (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) (hin : SublatticePlaqBound s V β)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s)
    (μ : Fin 3) (ell : ℕ) (acc rest : List (Fin 3))
    {g : SU2} (hg : g ∈ surfaceAlongS s V y μ ell acc rest) :
    frobNorm ((g : M2)-1) ≤ β := by
  induction rest generalizing acc with
  | nil => simp [surfaceAlongS] at hg
  | cons ν rest ih =>
      change g ∈ ((ladderFactorsS s V (coarsePathEndpoint s y acc) μ ν ell).map
        (conjBy (segmentHolS s V y μ ell *
          (holonomyFactors s V (coarseShift y (s*ell) μ) acc).prod))) ++
          surfaceAlongS s V y μ ell (acc ++ [ν]) rest at hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
        unfold conjBy
        rw [frobNorm_conj_sub_one]
        exact fitted_ladder_factor_bound s hd V β hin _ (path_endpoint_aligned s hd y hy acc)
          μ ν ell hq
      · exact ih (acc ++ [ν]) hg

theorem fitted_surface_norm (s : ℕ) (hd : ∀ μ : Fin 3, s ∣ L μ + 1)
    (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) (hβ : 0 ≤ β)
    (hin : SublatticePlaqBound s V β)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s)
    (μ : Fin 3) (ell : ℕ) (acc rest : List (Fin 3)) :
    frobNorm ((((surfaceAlongS s V y μ ell acc rest).prod : SU2) : M2)-1) ≤
      (ell : ℝ) * rest.length * β := by
  have h := frobNorm_prod_sub_one_le (surfaceAlongS s V y μ ell acc rest) β
    (fun g hg => fitted_surface_factor_bound s hd V β hin y hy μ ell acc rest hg)
  have hn : ((surfaceAlongS s V y μ ell acc rest).length : ℝ) ≤
      (ell : ℝ)*rest.length := by
    exact_mod_cast surfaceAlongS_length_le s V y μ ell acc rest
  exact h.trans (mul_le_mul_of_nonneg_right hn hβ)

/-- The contractible-loop premise in the new analytic theorem is discharged
from the EXACT fitted input, including small/wrapped periodic lattices. -/
theorem fitted_loop_norm (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ + 1)
    (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) (hβ : 0 ≤ β)
    (hin : SublatticePlaqBound s V β)
    (c : PeriodicLatticeEdge L) (hc : c.1 ∈ CoarseLattice L (s*ell))
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    frobNorm (((loopVar s ell V c x : SU2) : M2)-1) ≤ 3*((ell : ℝ)^2*β) := by
  have hds : ∀ μ : Fin 3, s ∣ L μ+1 := fun μ => dvd_trans (dvd_mul_right s ell) (hd μ)
  have hcs := coarseLattice_antitone (dvd_mul_right s ell) hc
  have hf : ∀ g ∈ loopSurfaceFactorsS s V ell c x, frobNorm ((g : M2)-1) ≤ β := by
    intro g hg
    exact fitted_surface_factor_bound s hds V β hin c.1 hcs c.2 ell []
      (coarseGammaPath s c.1 x) hg
  have h := frobNorm_prod_sub_one_le (loopSurfaceFactorsS s V ell c x) β hf
  rw [loopSurfaceFactorsS_prod s V ell c x hx] at h
  have hn : ((loopSurfaceFactorsS s V ell c x).length : ℝ) ≤ 3*(ell : ℝ)^2 := by
    have hlen := loopSurfaceFactorsS_length_le s hs V ell c x hx
    have hnat : (loopSurfaceFactorsS s V ell c x).length ≤ 3*ell*ell := by
      exact hlen.trans (Nat.mul_le_mul_left (3*ell) (Nat.sub_le ell 1))
    rw [pow_two, ← mul_assoc]
    exact_mod_cast hnat
  have hp := mul_le_mul_of_nonneg_right hn hβ
  nlinarith

/-- An ell by ell coarse rectangle has exactly the ell^2 linear budget on the
input sublattice. Individual coarse bonds need not be small. -/
theorem fitted_rectangle_norm (s ell : ℕ) (hd : ∀ μ : Fin 3, s ∣ L μ + 1)
    (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) (hβ : 0 ≤ β)
    (hin : SublatticePlaqBound s V β)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS (s*ell) (coarseBondVar s ell V) y μ ν : SU2) : M2)-1)
      ≤ (ell : ℝ)^2*β := by
  have hfill := surfaceAlongS_prod s V y ν ell [] (List.replicate ell μ)
  have h := fitted_surface_norm s hd V β hβ hin y hy ν ell [] (List.replicate ell μ)
  have hend : coarsePathEndpoint s y (List.replicate ell μ) = coarseShift y (s*ell) μ :=
    coarsePathEndpoint_replicate s y μ ell
  have heq : (surfaceAlongS s V y ν ell [] (List.replicate ell μ)).prod =
      orientedPlaqHolS (s*ell) (coarseBondVar s ell V) y μ ν := by
    have hempty : coarsePathEndpoint s y [] = y := rfl
    simpa [List.append, hempty, hend, segmentHolS, holonomyFactors_prod,
      orientedPlaqHolS, coarseBondVar, mul_assoc] using hfill
  rw [heq] at h
  simpa [List.length_replicate, pow_two] using h

end Prop1.ScaleFittedRepair

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedRepair.path_endpoint_aligned,
      `Prop1.ScaleFittedRepair.fitted_ladder_factor_bound,
      `Prop1.ScaleFittedRepair.fitted_surface_factor_bound,
      `Prop1.ScaleFittedRepair.fitted_surface_norm,
      `Prop1.ScaleFittedRepair.fitted_loop_norm,
      `Prop1.ScaleFittedRepair.fitted_rectangle_norm] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"FITTED_SURFACE_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "FITTED_SURFACES_COMPLETE"
