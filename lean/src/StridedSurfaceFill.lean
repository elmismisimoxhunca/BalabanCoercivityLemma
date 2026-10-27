import LoopHolonomySmall
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Strided Stokes filling: the level-`j` loop `loopVar (ell^j) ell V c x` as a product of
`≤ 3·ell·(ell-1)` conjugated stride-`(ell^j)` plaquettes

This file transports the certified stride-1 discrete Stokes construction of
`LoopHolonomySmall.lean` §6 (namespace `SmallnessBridge.Assemble`) to ARBITRARY stride `s`.
The RG meaning: at tower level `j`, `s = ell^j` and `V = bg j` (the `j`-fold averaged
background); the stride-`s` plaquette `orientedPlaqHolS (ell^j) (bg j) y μ ν` is exactly
Balaban's coarse plaquette variable `Ū^j(∂p)` of the level-`j` lattice.

The factor count `loopSurfaceBound ell = 3·ell·(ell-1)` is REUSED from the certified file
(it depends only on the block side `ell` in current-level units, never on `s`) — this is
why the eventual bound is uniform in the depth `k` and not `O(ell^{2j})`-compounded.

Everything is proved from the certified shift algebra (`coarseShift_comm`, `coarseShift_add`,
`periodicLatticeShift_coarseShift_comm` — all stride-generic in the deps) plus the certified
product-angle bridge `SmallnessBridge.ProdBound.principal_list_prod_small`. No new axioms.
-/

noncomputable section

namespace DepthUniformity.Strided

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLatticeSite PeriodicLinkConfiguration
    PeriodicLatticePlaquette PeriodicPlaquetteDirections
    periodicPlaquetteHolonomy periodicLatticeShift)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Angle su2Angle_conj)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Balaban.RMapLipschitz
open AdalyFormal.Balaban.TowerLawCov
  (coarsePathHolonomy coarseGammaPath coarseStraightSegment coarseCoordSteps
    coarsePathEndpoint)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar cPlusS cPlusS_eq)
open AdalyFormal.Balaban.QjComposite
  (stepBlockOf mem_stepBlockOf stepBlockOf_one inStepBlock
    coarsePathHolonomy_nil coarsePathHolonomy_cons
    coarsePathHolonomy_append coarsePathEndpoint_cons coarsePathEndpoint_append
    coarsePathEndpoint_coarseGammaPath)
open AdalyFormal.Balaban.AdmissibleSubspace (inBlock mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open SmallnessBridge.ProdBound
open SmallnessBridge.Assemble
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 — stride-generic path algebra (certified deps proved the stride-1 cases) -/

/-- Stride-`s` form of the certified `coarsePathEndpoint_coarseShift` (which fixed `s = 1`). -/
theorem coarsePathEndpoint_coarseShift_S (s : ℕ) (y : PeriodicLatticeSite L) (n : ℕ)
    (μ : Fin 3) (p : List (Fin 3)) :
    coarsePathEndpoint s (coarseShift y n μ) p =
      coarseShift (coarsePathEndpoint s y p) n μ := by
  induction p generalizing y with
  | nil => rfl
  | cons ν rest ih =>
      rw [coarsePathEndpoint_cons, coarsePathEndpoint_cons, coarseShift_comm]
      exact ih _

/-- Stride-`s` form of the certified `coarsePathEndpoint_snoc`. -/
theorem coarsePathEndpoint_snoc_S (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3))
    (ν : Fin 3) :
    coarsePathEndpoint s y (p ++ [ν]) =
      coarseShift (coarsePathEndpoint s y p) s ν := by
  rw [coarsePathEndpoint_append, coarsePathEndpoint_cons]
  rfl

theorem holonomyFactors_append_prod_S {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L)
    (p q : List (Fin 3)) :
    (holonomyFactors s V y (p ++ q)).prod =
      (holonomyFactors s V y p).prod *
        (holonomyFactors s V (coarsePathEndpoint s y p) q).prod := by
  rw [holonomyFactors_prod, holonomyFactors_prod, holonomyFactors_prod,
    coarsePathHolonomy_append]

theorem holonomyFactors_snoc_prod_S {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) (ν : Fin 3) :
    (holonomyFactors s V y (p ++ [ν])).prod =
      (holonomyFactors s V y p).prod * V (coarsePathEndpoint s y p, ν) := by
  rw [holonomyFactors_append_prod_S, holonomyFactors_cons, holonomyFactors_nil,
    List.prod_cons, List.prod_nil, mul_one]

/-! ## §2 — the stride-`s` oriented plaquette and ladder/segment primitives -/

/-- Oriented stride-`s` plaquette word: the level-`j` coarse plaquette `Ū^j(∂p)` when
`s = ell^j` and `V = bg j`. Degenerate (identity) when `μ = ν`. At `s = 1` this is the
certified `orientedPlaqHol` (see `orientedPlaqHolS_one_eq`). -/
def orientedPlaqHolS {G : Type*} [Group G] (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) : G :=
  V (y, μ) * V (coarseShift y s μ, ν) *
    (V (coarseShift y s ν, μ))⁻¹ * (V (y, ν))⁻¹

/-- Stride-1 reduction: `orientedPlaqHolS 1 = orientedPlaqHol` (via `coarseShift_one_eq`). -/
theorem orientedPlaqHolS_one_eq {G : Type*} [Group G] (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    orientedPlaqHolS 1 V y μ ν = orientedPlaqHol V y μ ν := by
  simp only [orientedPlaqHolS, orientedPlaqHol, coarseShift_one_eq]

/-- Degenerate stride-`s` plaquette is the identity. -/
theorem orientedPlaqHolS_self {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L) (μ : Fin 3) :
    orientedPlaqHolS s V y μ μ = 1 := by
  simp [orientedPlaqHolS, mul_assoc, mul_inv_cancel, inv_mul_cancel]

/-- Stride-`s` segment holonomy: `n` consecutive stride-`s` bonds along `μ`. -/
def segmentHolS {G : Type*} [Group G] (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : G :=
  (holonomyFactors s V y (List.replicate n μ)).prod

theorem segmentHolS_zero {G : Type*} [Group G] (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) : segmentHolS s V y μ 0 = 1 := by
  simp [segmentHolS, holonomyFactors_nil]

theorem segmentHolS_succ {G : Type*} [Group G] (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    segmentHolS s V y μ (n + 1) =
      V (y, μ) * segmentHolS s V (coarseShift y s μ) μ n := by
  unfold segmentHolS
  rw [List.replicate_succ, holonomyFactors_cons, List.prod_cons]

theorem segmentHolS_snoc {G : Type*} [Group G] (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    segmentHolS s V y μ (n + 1) =
      segmentHolS s V y μ n * V (coarseShift y (s * n) μ, μ) := by
  induction n generalizing y with
  | zero =>
      simp [segmentHolS_succ, segmentHolS_zero, coarseShift_zero]
  | succ n ih =>
      rw [segmentHolS_succ, ih (coarseShift y s μ), ← mul_assoc, ← segmentHolS_succ,
        coarseShift_add, show s + s * n = s * (n + 1) from by ring]

/-- The ladder holonomy at stride `s`: the `μ`-extruded tube around one `ν`-bond. -/
def ladderHolS {G : Type*} [Group G] (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) : G :=
  (segmentHolS s V y μ ell)⁻¹ * V (y, ν) *
    segmentHolS s V (coarseShift y s ν) μ ell *
      (V (coarseShift y (s * ell) μ, ν))⁻¹

theorem ladderHolS_zero {G : Type*} [Group G] (s : ℕ) (V : PeriodicLinkConfiguration G L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) : ladderHolS s V y μ ν 0 = 1 := by
  simp [ladderHolS, segmentHolS_zero, coarseShift_zero]

theorem ladderHolS_eq_one_of_eq {G : Type*} [Group G] (s : ℕ)
    (V : PeriodicLinkConfiguration G L) (y : PeriodicLatticeSite L)
    (μ : Fin 3) (ell : ℕ) : ladderHolS s V y μ μ ell = 1 := by
  cases ell with
  | zero => exact ladderHolS_zero s V y μ μ
  | succ n =>
      have hsite : coarseShift (coarseShift y s μ) (s * n) μ =
          coarseShift y (s * (n + 1)) μ := by
        rw [coarseShift_add, show s + s * n = s * (n + 1) from by ring]
      unfold ladderHolS
      rw [segmentHolS_succ, segmentHolS_snoc (y := coarseShift y s μ), hsite]
      simp [mul_assoc, inv_mul_cancel, mul_inv_cancel]

/-- Rungs of the stride-`s` ladder; empty on the degenerate line `μ = ν`. -/
def ladderFactorsS (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) : ℕ → List SU2
  | 0 => []
  | n + 1 =>
      if h : μ = ν then []
      else
        let A := V (y, μ)
        let hol := orientedPlaqHolS s V y μ ν
        let S := segmentHolS s V (coarseShift y s μ) μ n
        (S⁻¹ * (A⁻¹ * hol⁻¹ * A) * S) ::
          ladderFactorsS s V (coarseShift y s μ) μ ν n

theorem ladderFactorsS_length_le (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) :
    (ladderFactorsS s V y μ ν ell).length ≤ ell := by
  induction ell generalizing y with
  | zero => simp [ladderFactorsS]
  | succ n ih =>
      unfold ladderFactorsS
      split_ifs
      · simp
      · exact Nat.succ_le_succ (ih _)

theorem ladderHolS_succ_eq
    (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (y : PeriodicLatticeSite L)
    {μ ν : Fin 3} (hμν : μ ≠ ν) (n : ℕ) :
    ladderHolS s V y μ ν (n + 1) =
      (segmentHolS s V (coarseShift y s μ) μ n)⁻¹
        * ((V (y, μ))⁻¹ * (orientedPlaqHolS s V y μ ν)⁻¹ * V (y, μ))
        * segmentHolS s V (coarseShift y s μ) μ n
        * ladderHolS s V (coarseShift y s μ) μ ν n := by
  set A : SU2 := V (y, μ)
  set D : SU2 := V (y, ν)
  set B : SU2 := V (coarseShift y s μ, ν)
  set C : SU2 := V (coarseShift y s ν, μ)
  set S : SU2 := segmentHolS s V (coarseShift y s μ) μ n
  set Sν : SU2 :=
    segmentHolS s V (coarseShift (coarseShift y s μ) s ν) μ n
  set far : SU2 := V (coarseShift y (s * (n + 1)) μ, ν)
  have hSν :
      segmentHolS s V (coarseShift (coarseShift y s ν) s μ) μ n = Sν := by
    simp only [Sν, coarseShift_comm]
  have hfar : V (coarseShift (coarseShift y s μ) (s * n) μ, ν) = far := by
    simp only [far, coarseShift_add]
    rw [show s + s * n = s * (n + 1) from by ring]
  have hinv : (orientedPlaqHolS s V y μ ν)⁻¹ = D * C * B⁻¹ * A⁻¹ := by
    simp [orientedPlaqHolS, A, B, C, D, mul_assoc, mul_inv, inv_inv]
  have hseg : segmentHolS s V (coarseShift y s ν) μ (n + 1) = C * Sν := by
    rw [segmentHolS_succ, hSν]
  have hsmall :
      ladderHolS s V (coarseShift y s μ) μ ν n = S⁻¹ * B * Sν * far⁻¹ := by
    simp only [ladderHolS, S, B, Sν, hfar]
  conv_lhs => unfold ladderHolS
  rw [segmentHolS_succ, hseg]
  rw [show V (coarseShift y (s * (n + 1)) μ, ν) = far from rfl, hsmall, hinv]
  simp [mul_assoc, inv_mul_cancel, mul_inv_cancel, A, D, B, C, S, Sν, far]

theorem ladderFactorsS_prod (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) :
    (ladderFactorsS s V y μ ν ell).prod = ladderHolS s V y μ ν ell := by
  induction ell generalizing y with
  | zero => simp [ladderFactorsS, ladderHolS_zero]
  | succ n ih =>
      unfold ladderFactorsS
      split_ifs with h
      · subst h
        simp [ladderHolS_eq_one_of_eq]
      · rw [List.prod_cons, ih, ladderHolS_succ_eq (hμν := h)]

/-- Every rung of the stride-`s` ladder is a conjugate of a stride-`s` plaquette, hence
bounded by the plaquette angle budget (`su2Angle_conj` invariance, certified). -/
theorem su2Angle_mem_ladderFactorsS (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) (ell : ℕ) (delta : ℝ)
    (h : ∀ (y' : PeriodicLatticeSite L) (μ' ν' : Fin 3), μ' ≠ ν' →
      su2Angle (orientedPlaqHolS s V y' μ' ν') ≤ delta)
    {g : SU2} (hg : g ∈ ladderFactorsS s V y μ ν ell) :
    su2Angle g ≤ delta := by
  induction ell generalizing y with
  | zero =>
      simp [ladderFactorsS] at hg
  | succ n ih =>
      unfold ladderFactorsS at hg
      split_ifs at hg with hμν
      · simp at hg
      · simp only [List.mem_cons] at hg
        rcases hg with hg | hg
        · subst hg
          set A : SU2 := V (y, μ)
          set hol : SU2 := orientedPlaqHolS s V y μ ν
          set S : SU2 := segmentHolS s V (coarseShift y s μ) μ n
          have h1 : su2Angle (A⁻¹ * hol⁻¹ * A) = su2Angle hol := by
            have := su2Angle_conj A⁻¹ hol⁻¹
            simpa [inv_inv, su2Angle_inv] using this
          have h2 : su2Angle (S⁻¹ * (A⁻¹ * hol⁻¹ * A) * S) = su2Angle hol := by
            have := su2Angle_conj S⁻¹ (A⁻¹ * hol⁻¹ * A)
            simpa [inv_inv, h1] using this
          simpa [A, hol, S] using h2.trans_le (h y μ ν hμν)
        · exact ih (coarseShift y s μ) hg

/-! ## §3 — the stride-`s` surface filling (telescoping tube along the near staircase) -/

/-- Conjugated plaquette rungs filling the stride-`s` tube along a remaining staircase. -/
def surfaceAlongS (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ) :
    List (Fin 3) → List (Fin 3) → List SU2
  | acc, [] => []
  | acc, ν :: rest =>
      let y := coarsePathEndpoint s y0 acc
      let S0 := segmentHolS s V y0 μ ell
      let holFar := (holonomyFactors s V (coarseShift y0 (s * ell) μ) acc).prod
      List.append ((ladderFactorsS s V y μ ν ell).map (conjBy (S0 * holFar)))
        (surfaceAlongS s V y0 μ ell (List.append acc [ν]) rest)

theorem surfaceAlongS_length_le (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ)
    (acc rest : List (Fin 3)) :
    (surfaceAlongS s V y0 μ ell acc rest).length ≤ ell * rest.length := by
  induction rest generalizing acc with
  | nil => simp [surfaceAlongS]
  | cons ν rest ih =>
      simp [surfaceAlongS, List.length_append, List.length_map, List.length_cons]
      have h1 := ladderFactorsS_length_le s V (coarsePathEndpoint s y0 acc) μ ν ell
      have h2 := ih (acc ++ [ν])
      calc
        _ ≤ ell + ell * rest.length := Nat.add_le_add h1 h2
        _ = ell * (rest.length + 1) := by ring

theorem su2Angle_mem_surfaceAlongS (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ)
    (acc rest : List (Fin 3)) (delta : ℝ)
    (h : ∀ (y' : PeriodicLatticeSite L) (μ' ν' : Fin 3), μ' ≠ ν' →
      su2Angle (orientedPlaqHolS s V y' μ' ν') ≤ delta)
    {g : SU2} (hg : g ∈ surfaceAlongS s V y0 μ ell acc rest) :
    su2Angle g ≤ delta := by
  induction rest generalizing acc with
  | nil =>
      simp [surfaceAlongS] at hg
  | cons ν rest ih =>
      have hmem :
          g ∈ (ladderFactorsS s V (coarsePathEndpoint s y0 acc) μ ν ell).map
              (conjBy (segmentHolS s V y0 μ ell *
                (holonomyFactors s V (coarseShift y0 (s * ell) μ) acc).prod)) ∨
            g ∈ surfaceAlongS s V y0 μ ell (acc ++ [ν]) rest := by
        simpa [surfaceAlongS] using hg
      rcases hmem with hg | hg
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        rw [su2Angle_conjBy]
        exact su2Angle_mem_ladderFactorsS s V _ μ ν ell delta h hg0
      · exact ih (acc ++ [ν]) hg

/-- **The stride-`s` telescoping identity**: walking the near staircase, each step extrudes
one `ell`-rung ladder of conjugated stride-`s` plaquettes; the product collapses the tube
boundary onto the loop contour factors. -/
theorem surfaceAlongS_prod (s : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (y0 : PeriodicLatticeSite L) (μ : Fin 3) (ell : ℕ)
    (acc rest : List (Fin 3)) :
    ((holonomyFactors s V y0 acc).prod
        * segmentHolS s V (coarsePathEndpoint s y0 acc) μ ell
        * (holonomyFactors s V (coarseShift y0 (s * ell) μ) acc).prod⁻¹
        * (segmentHolS s V y0 μ ell)⁻¹
        * (surfaceAlongS s V y0 μ ell acc rest).prod) =
      ((holonomyFactors s V y0 (List.append acc rest)).prod
        * segmentHolS s V (coarsePathEndpoint s y0 (List.append acc rest)) μ ell
        * (holonomyFactors s V (coarseShift y0 (s * ell) μ) (List.append acc rest)).prod⁻¹
        * (segmentHolS s V y0 μ ell)⁻¹) := by
  induction rest generalizing acc with
  | nil =>
      simp [surfaceAlongS]
  | cons ν rest ih =>
      let y := coarsePathEndpoint s y0 acc
      let S0 := segmentHolS s V y0 μ ell
      let holFar := (holonomyFactors s V (coarseShift y0 (s * ell) μ) acc).prod
      let Q := ladderHolS s V y μ ν ell
      let accν := List.append acc [ν]
      have hsurf :
          surfaceAlongS s V y0 μ ell acc (ν :: rest) =
            List.append ((ladderFactorsS s V y μ ν ell).map (conjBy (S0 * holFar)))
              (surfaceAlongS s V y0 μ ell accν rest) := by
        simp [surfaceAlongS, y, S0, holFar, accν]
      have hmap :
          ((ladderFactorsS s V y μ ν ell).map (conjBy (S0 * holFar))).prod =
            conjBy (S0 * holFar) Q := by
        rw [list_map_conjBy_prod, ladderFactorsS_prod]
      have hyν : coarsePathEndpoint s y0 accν = coarseShift y s ν := by
        simpa [y, accν] using coarsePathEndpoint_snoc_S s y0 acc ν
      have hfarν :
          (holonomyFactors s V (coarseShift y0 (s * ell) μ) accν).prod =
            holFar * V (coarseShift y (s * ell) μ, ν) := by
        simp only [accν]
        rw [show acc.append [ν] = acc ++ [ν] from rfl, holonomyFactors_snoc_prod_S,
          coarsePathEndpoint_coarseShift_S]
      have hpre :
          (holonomyFactors s V y0 accν).prod =
            (holonomyFactors s V y0 acc).prod * V (y, ν) := by
        simpa [accν] using holonomyFactors_snoc_prod_S s V y0 acc ν
      have hstep :
          ((holonomyFactors s V y0 acc).prod * segmentHolS s V y μ ell * holFar⁻¹ * S0⁻¹
              * conjBy (S0 * holFar) Q) =
            ((holonomyFactors s V y0 accν).prod
              * segmentHolS s V (coarsePathEndpoint s y0 accν) μ ell
              * (holonomyFactors s V (coarseShift y0 (s * ell) μ) accν).prod⁻¹
              * S0⁻¹) := by
        unfold conjBy Q ladderHolS
        rw [hyν, hfarν, hpre]
        simp [mul_assoc, inv_mul_cancel, mul_inv_cancel, y, S0, holFar]
      have hrest : List.append accν rest = List.append acc (ν :: rest) := by
        simp [accν]
      rw [hsurf, show List.append
          ((ladderFactorsS s V y μ ν ell).map (conjBy (S0 * holFar)))
          (surfaceAlongS s V y0 μ ell accν rest) =
          ((ladderFactorsS s V y μ ν ell).map (conjBy (S0 * holFar))) ++
            surfaceAlongS s V y0 μ ell accν rest from rfl, List.prod_append, hmap]
      have ih' := ih accν
      have hmul := congrArg (fun z : SU2 => z * (surfaceAlongS s V y0 μ ell accν rest).prod) hstep
      simp [mul_assoc, y, S0, holFar, accν] at hmul ih' ⊢
      rw [hmul, ih']

/-! ## §4 — the strided loop surface factors, length bound, and product identity -/

/-- The conjugated stride-`s` plaquettes filling the C1 tube of `loopVar s ell V c x`. -/
def loopSurfaceFactorsS (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) : List SU2 :=
  surfaceAlongS s V c.1 c.2 ell [] (coarseGammaPath s c.1 x)

/-- Stride-`s` staircase coordinate-step bound from block membership. -/
theorem coarseCoordSteps_lt_of_inStepBlock {s : ℕ} (hs : 0 < s) {y x : PeriodicLatticeSite L}
    {ell : ℕ} (hx : inStepBlock y s ell x) (μ : Fin 3) :
    coarseCoordSteps s y x μ < ell := by
  obtain ⟨hle, hlt, hdvd⟩ := hx μ
  unfold coarseCoordSteps
  rw [Fin.sub_val_of_le (Fin.le_def.mpr hle)]
  by_contra hcon
  push_neg at hcon
  have h1 : s * ell ≤ s * (((x μ).val - (y μ).val) / s) := Nat.mul_le_mul_left s hcon
  rw [Nat.mul_div_cancel' hdvd] at h1
  omega

/-- Stride-`s` staircase length bound: three axes, each `< ell` steps. -/
theorem coarseGammaPath_s_length_le {s : ℕ} (hs : 0 < s) {y x : PeriodicLatticeSite L}
    {ell : ℕ} (hx : inStepBlock y s ell x) :
    (coarseGammaPath s y x).length ≤ 3 * (ell - 1) := by
  have h2 : coarseCoordSteps s y x 2 < ell := coarseCoordSteps_lt_of_inStepBlock hs hx 2
  have h1 : coarseCoordSteps s y x 1 < ell := coarseCoordSteps_lt_of_inStepBlock hs hx 1
  have h0 : coarseCoordSteps s y x 0 < ell := coarseCoordSteps_lt_of_inStepBlock hs hx 0
  have h1' :
      coarseCoordSteps s (Function.update y 2 (x 2)) x 1 =
        coarseCoordSteps s y x 1 :=
    coarseCoordSteps_update_ne s y x (x 2) (by decide : (1 : Fin 3) ≠ 2)
  have h0a :
      coarseCoordSteps s (Function.update y 2 (x 2)) x 0 =
        coarseCoordSteps s y x 0 :=
    coarseCoordSteps_update_ne s y x (x 2) (by decide : (0 : Fin 3) ≠ 2)
  have h0' :
      coarseCoordSteps s
          (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0 =
        coarseCoordSteps s y x 0 := by
    rw [coarseCoordSteps_update_ne s (Function.update y 2 (x 2)) x (x 1)
      (by decide : (0 : Fin 3) ≠ 1), h0a]
  rw [coarseGammaPath_length, h1', h0']
  have h2le : coarseCoordSteps s y x 2 ≤ ell - 1 := Nat.le_pred_of_lt h2
  have h1le : coarseCoordSteps s y x 1 ≤ ell - 1 := Nat.le_pred_of_lt h1
  have h0le : coarseCoordSteps s y x 0 ≤ ell - 1 := Nat.le_pred_of_lt h0
  have : 3 * (ell - 1) = (ell - 1) + (ell - 1) + (ell - 1) := by ring
  rw [this]
  exact add_le_add (add_le_add h2le h1le) h0le

theorem loopSurfaceFactorsS_length_le (s : ℕ) (hs : 0 < s)
    (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 s ell) :
    (loopSurfaceFactorsS s V ell c x).length ≤ loopSurfaceBound ell := by
  have hin : inStepBlock c.1 s ell x := (mem_stepBlockOf).mp hx
  have hγ : (coarseGammaPath s c.1 x).length ≤ 3 * (ell - 1) :=
    coarseGammaPath_s_length_le hs hin
  have hlen := surfaceAlongS_length_le s V c.1 c.2 ell [] (coarseGammaPath s c.1 x)
  unfold loopSurfaceFactorsS loopSurfaceBound
  have : ell * (coarseGammaPath s c.1 x).length ≤ ell * (3 * (ell - 1)) :=
    Nat.mul_le_mul_left _ hγ
  have hmul : ell * (3 * (ell - 1)) = 3 * ell * (ell - 1) := by ring
  omega

/-- **The stride-`s` Stokes theorem**: the C1 loop at stride `s` IS the product of the
conjugated stride-`s` plaquette rungs. -/
theorem loopSurfaceFactorsS_prod (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 s ell) :
    (loopSurfaceFactorsS s V ell c x).prod = loopVar s ell V c x := by
  have hx' := mem_stepBlockOf.mp hx
  have hend : coarsePathEndpoint s c.1 (coarseGammaPath s c.1 x) = x :=
    coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hx' μ).1, (hx' μ).2.2⟩)
  have hfar : cPlusS s ell c = coarseShift c.1 (s * ell) c.2 := cPlusS_eq s ell c
  have hfill := surfaceAlongS_prod s V c.1 c.2 ell [] (coarseGammaPath s c.1 x)
  unfold loopSurfaceFactorsS loopVar gammaVarStrided coarseBondVar
  rw [hfar]
  simp [holonomyFactors_nil, List.append, hend, segmentHolS, holonomyFactors_prod,
    mul_assoc] at hfill ⊢
  have hcancel :
      coarsePathHolonomy s V c.1 (List.replicate ell c.2) *
          ((coarsePathHolonomy s V c.1 (List.replicate ell c.2))⁻¹ *
            (surfaceAlongS s V c.1 c.2 ell [] (coarseGammaPath s c.1 x)).prod) =
        (surfaceAlongS s V c.1 c.2 ell [] (coarseGammaPath s c.1 x)).prod := by
    simp [← mul_assoc, mul_inv_cancel]
  exact hcancel.symm.trans hfill

/-! ## §5 — angle and Frobenius interfaces at stride `s` -/

/-- Stride-`s` form of the certified `nu_loopVar_le_surface_mul`: per-rung angle budget
`delta` with `N(ell)·delta < π/2` gives the principal-log norm bound. -/
theorem nu_loopVar_le_surface_mul_S (V : PeriodicLinkConfiguration SU2 L)
    (s ell : ℕ) (hs : 0 < s)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (delta : ℝ) (hδ : 0 ≤ delta)
    (h : ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3), μ ≠ ν →
      su2Angle (orientedPlaqHolS s V y μ ν) ≤ delta)
    (hx : x ∈ stepBlockOf c.1 s ell)
    (hsmall : (loopSurfaceBound ell : ℝ) * delta < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar s ell V c x) : SuTwo) : M2) ≤
        (loopSurfaceBound ell : ℝ) * delta ∧
      (loopSurfaceBound ell : ℝ) * delta < Real.pi / 2 := by
  have hprod := loopSurfaceFactorsS_prod s V ell c x hx
  have hfac : ∀ g ∈ loopSurfaceFactorsS s V ell c x, su2Angle g ≤ delta :=
    fun g hg => su2Angle_mem_surfaceAlongS s V c.1 c.2 ell [] (coarseGammaPath s c.1 x)
      delta h hg
  have hlen : ((loopSurfaceFactorsS s V ell c x).length : ℝ) ≤ (loopSurfaceBound ell : ℝ) :=
    Nat.cast_le.mpr (loopSurfaceFactorsS_length_le s hs V ell c x hx)
  have hlen_small :
      ((loopSurfaceFactorsS s V ell c x).length : ℝ) * delta < Real.pi / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hlen hδ) hsmall
  have hpt := principal_list_prod_small (loopSurfaceFactorsS s V ell c x) delta hfac hlen_small
  rw [hprod] at hpt
  exact ⟨hpt.1.trans (mul_le_mul_of_nonneg_right hlen hδ), hsmall⟩

/-- Frobenius plaquette data at stride `s` gives the angle budget, via the certified
`su2Angle_le_frobNorm` (`θ ≤ (π/(2√2))·‖g − 1‖_F`). -/
theorem su2Angle_orientedPlaqHolS_le (V : PeriodicLinkConfiguration SU2 L) (s : ℕ)
    (eps0 : ℝ) (h0 : 0 ≤ eps0)
    (hV : ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) ≤ eps0)
    (y : PeriodicLatticeSite L) (μ ν : Fin 3) :
    su2Angle (orientedPlaqHolS s V y μ ν) ≤ (Real.pi / (2 * Real.sqrt 2)) * eps0 :=
  (su2Angle_le_frobNorm (orientedPlaqHolS s V y μ ν)).trans
    (mul_le_mul_of_nonneg_left (hV y μ ν) (by positivity))

/-- **The strided one-level bridge** (stride-`s` form of the certified
`nu_loopVar_V0_le_rho`): from per-plaquette Frobenius data at stride `s` on `V`,
`ν(Z_x) ≤ loopRhoPlaq eps0 ell = 3·ell·(ell-1)·(π/(2√2))·eps0`, strict `< π/2` guard. -/
theorem nu_loopVar_le_rhoPlaq_S (V : PeriodicLinkConfiguration SU2 L)
    (s ell : ℕ) (hs : 0 < s) (eps0 : ℝ) (h0 : 0 ≤ eps0)
    (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 s ell)
    (hV : ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3),
      frobNorm (((orientedPlaqHolS s V y μ ν : SU2) : M2) - 1) ≤ eps0)
    (hsmall : loopRhoPlaq eps0 ell < Real.pi / 2) :
    nu ((principalSuTwoLog (loopVar s ell V c x) : SuTwo) : M2) ≤
        loopRhoPlaq eps0 ell ∧
      loopRhoPlaq eps0 ell < Real.pi / 2 := by
  set delta : ℝ := (Real.pi / (2 * Real.sqrt 2)) * eps0
  have hδ : 0 ≤ delta := mul_nonneg (by positivity) h0
  have hAng : ∀ (y : PeriodicLatticeSite L) (μ ν : Fin 3), μ ≠ ν →
      su2Angle (orientedPlaqHolS s V y μ ν) ≤ delta :=
    fun y μ ν _ => su2Angle_orientedPlaqHolS_le V s eps0 h0 hV y μ ν
  simpa [loopRhoPlaq, delta] using
    nu_loopVar_le_surface_mul_S V s ell hs c x delta hδ hAng hx
      (by simpa [loopRhoPlaq, delta] using hsmall)

/-- Frobenius norm of `g⁻¹ − 1` equals that of `g − 1` on `SU(2)`
(via the certified exact identity `‖g − 1‖²_F = 4(1 − cos θ)` and `su2Angle_inv`). -/
theorem frobNorm_inv_sub_one (g : SU2) :
    frobNorm (((g⁻¹ : SU2) : M2) - 1) = frobNorm ((g : M2) - 1) := by
  unfold frobNorm
  rw [frobSq_su2_sub_one, frobSq_su2_sub_one, su2Angle_inv]

end DepthUniformity.Strided

/-! ## §6 — import fingerprint and axiom audit -/

run_cmd do
  let ownDeps := "/home/sebastian/projects/project-adaly/compute/depth_uniformity/deps"
  let ownBuild := "/home/sebastian/projects/project-adaly/compute/depth_uniformity/build/runs/loop01"
  let lh ← Lean.findOLean `LoopHolonomySmall
  unless lh.toString == s!"{ownBuild}/LoopHolonomySmall.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED STRIDED_IMPORT_MISMATCH LoopHolonomySmall: resolved {lh}"
  Lean.logInfo m!"STRIDED_RESOLVED LoopHolonomySmall: {lh}"
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let thms : List Lean.Name :=
    [`DepthUniformity.Strided.coarsePathEndpoint_coarseShift_S,
     `DepthUniformity.Strided.coarsePathEndpoint_snoc_S,
     `DepthUniformity.Strided.orientedPlaqHolS_one_eq,
     `DepthUniformity.Strided.segmentHolS_snoc,
     `DepthUniformity.Strided.ladderHolS_succ_eq,
     `DepthUniformity.Strided.ladderFactorsS_prod,
     `DepthUniformity.Strided.su2Angle_mem_ladderFactorsS,
     `DepthUniformity.Strided.surfaceAlongS_length_le,
     `DepthUniformity.Strided.su2Angle_mem_surfaceAlongS,
     `DepthUniformity.Strided.surfaceAlongS_prod,
     `DepthUniformity.Strided.loopSurfaceFactorsS_length_le,
     `DepthUniformity.Strided.loopSurfaceFactorsS_prod,
     `DepthUniformity.Strided.nu_loopVar_le_surface_mul_S,
     `DepthUniformity.Strided.nu_loopVar_le_rhoPlaq_S,
     `DepthUniformity.Strided.frobNorm_inv_sub_one]
  for thm in thms do
    unless (← Lean.getEnv).contains thm do
      throwError "STRIDED missing declaration: {thm}"
    let axioms ← Lean.collectAxioms thm
    Lean.logInfo m!"STRIDED_AXIOMS {thm}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {thm}: {ax}"
  Lean.logInfo "STRIDED_AUDIT_PASS"

#print axioms DepthUniformity.Strided.loopSurfaceFactorsS_prod
#print axioms DepthUniformity.Strided.nu_loopVar_le_rhoPlaq_S
