import NC3
import NC1
import RI6

/-!
# GenCl1 -- the GENERAL class-cube reading of CMP99b p.396 (lane general_class_20261015)

Page image (corpus/renders/CMP99b_p396-08.png), verbatim:
"For each cube □ of this class there exists a unique index j, 0 ≤ j ≤ k, such that □ ⊂ B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1}),
 □ ∩ B^j(Λ_j) ≠ ∅, and □ is a union of several big blocks of the lattice T_{L^{-j}}, which implies that its size in the lattice
 T_η is O(1)ML^jη. Here O(1) will mean a number ≥ 10."
(3.35): "|A| < O(1)Mα₀(L^jη)^{-1}, |∇^ηA| < O(1)Mα₀(L^jη)^{-2} on □, where O(1)M is a size of □ in T_{L^{-j}};"
after (3.36): "We will need α₀ so small that O(1)Mα₀ is still a sufficiently small number."

Encoding (choices W1-W5 in NOTES.md):
* `IsClassCubeG ell M f k S sites j`: `10 ≤ f`, `sites` is the axis box of side `f · M · ell^j` with corner on the level-`j` grid
  (r8's `DescribedAt` with the factor `f` FREE per cube), and the index is unique over ALL factors `f'`.
* `CubeRegular ell M f sites j α₀ η U`: (3.35)+(3.36) on that cube with THAT cube's `f` (body of r8 `PerCubeRegular2`, verbatim).
* `PerCubeRegularG ell M F k S α₀ η U`: every general class cube of factor `f ≤ F` is regular with its own `f`.
* `P428Target8G F`: r8's `P428Target8` text with the class hypothesis `PerCubeRegularG .. F ..`, the smallness `F·M·α₀ ≤ a₀`, and
  NO coverage hypothesis.  `F` is fixed before `ell`.
* `IsClassSetW`: the non-box alternative (any set meeting at least two level-`j` blocks, enclosed in a box of side `F·M·ell^j`);
  it CONTAINS every general class cube (`isClassCubeG_toW`) and is used only for refutation.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.GeneralClass

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

/-! ## 1. definitions -/

/-- **general class cube** (p.396): box of side `f·M·ell^j` on the level-`j` grid, `□ ⊂ B^j ∪ B^{j+1}`, `□ ∩ B^j ≠ ∅`, `j ≤ k`,
per-cube factor `f ≥ 10`, and the index `j` unique among ALL descriptions (any factor). -/
def IsClassCubeG {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  10 ≤ f ∧ DescribedAt ell M f k S sites j ∧ ∀ i f' : ℕ, DescribedAt ell M f' k S sites i → i = j

/-- (3.35)+(3.36) on one cube with factor `f` (the body of r8 `PerCubeRegular2`, verbatim). -/
def CubeRegular {L : PeriodicLatticeExtent} (ell M f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e : Bond L, CubeBond sites e →
        HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
      (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        CubeBond sites ((x, ν) : Bond L) → CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        (∀ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧
          CurlReads sites x ν μ) →
        frobNorm (ddA η A x μ)
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

/-- pin: r8's class is `CubeRegular` on every r8 class cube. -/
theorem perCubeRegular2_iff {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) :
    PerCubeRegular2 ell M f k S α₀ η U ↔
      ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j → CubeRegular ell M f sites j α₀ η U :=
  Iff.rfl

/-- **the general class**: every general class cube of factor `f ≤ F` satisfies (3.35)+(3.36) with its own `f`. -/
def PerCubeRegularG {L : PeriodicLatticeExtent} (ell M F k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), f ≤ F → IsClassCubeG ell M f k S sites j →
    CubeRegular ell M f sites j α₀ η U

/-- the inner claim with the general class and NO coverage hypothesis. -/
def CoercG8AtG (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (F : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    PerCubeRegularG ell M F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

/-- constants block: `F·M·α₀ ≤ a₀` ("O(1)Mα₀ sufficiently small" with every per-cube `O(1) ≤ F`). -/
def P428Core8AtG (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (F : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (F : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtG ell M R k hell a Lu F α₀ γ₀

def P428Genuine8G (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (F : ℕ) : Prop :=
  SidePow6 ell M a ∧ P428Core8AtG ell M R hell a F

/-- **`P428Target8G F`**: the headline over the general class (per-cube factors in `[10, F]`), WITHOUT any coverage hypothesis. -/
def P428Target8G (F : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8G ell (ell ^ m) R (by omega) a F

/-- the general-class headline WITH r8's coverage hypothesis at factor 12 (the version the proved r8 theorem yields). -/
def CoercG8AtGC (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (F : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    CoversOm0p ell M 12 k S → PerCubeRegularG ell M F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

def P428Target8GC (F : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (F : ℝ) * (ell ^ m : ℕ) * α₀ ≤ a₀ →
          CoercG8AtGC ell (ell ^ m) R k (by omega) a Lu F α₀ γ₀

/-- the non-box superset used for refutation: index `j ≤ k`, `⊂ B^j ∪ B^{j+1}`, meets `B^j`, enclosed in a box of side
`F·M·ell^j`, and not inside a single level-`j` block. -/
def IsClassSetW {L : PeriodicLatticeExtent} (ell M F k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  j ≤ k ∧ sites ⊆ towerBj S j ∪ towerBj S (j + 1) ∧ (sites ∩ towerBj S j).Nonempty ∧
  (∃ z : PeriodicLatticeSite L, sites ⊆ siteBox z (F * bigSide M ell j)) ∧
  ∃ a ∈ sites, ∃ b ∈ sites, ∃ μ : Fin 3, (a μ).val / bigSide M ell j ≠ (b μ).val / bigSide M ell j

/-- coverage of the sites of `Ω₀` by general class cubes with factor `≤ F`. -/
def CoversOm0G {L : PeriodicLatticeExtent} (ell M F k : ℕ) (S : Tower L) : Prop :=
  ∀ x ∈ S.Om 0, ∃ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), f ≤ F ∧ IsClassCubeG ell M f k S sites j ∧ x ∈ sites

/-! ## 2. the unique-index clause is redundant on monotone towers -/

theorem om_anti {L : PeriodicLatticeExtent} {S : Tower L} (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j)
    {a b : ℕ} (hab : a ≤ b) : S.Om b ⊆ S.Om a := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact (hmono n).trans ih

theorem describedAt_index_unique {L : PeriodicLatticeExtent} {ell M f f' k : ℕ} {S : Tower L}
    (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) {sites : Set (PeriodicLatticeSite L)} {i i' : ℕ}
    (h : DescribedAt ell M f k S sites i) (h' : DescribedAt ell M f' k S sites i') : i = i' := by
  have key : ∀ {a b : ℕ} {fa fb : ℕ}, a < b → DescribedAt ell M fa k S sites a → DescribedAt ell M fb k S sites b → False := by
    intro a b fa fb hab ha hb
    obtain ⟨-, -, -, ⟨w, hw, hwB⟩⟩ := ha
    obtain ⟨-, -, hsub, -⟩ := hb
    have hw' := hsub hw
    have hwb : w ∈ S.Om b := by
      rcases hw' with h1 | h1
      · exact h1.1
      · exact om_anti hmono (Nat.le_succ b) h1.1
    exact hwB.2 (om_anti hmono (show a + 1 ≤ b by omega) hwb)
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact (key hlt h h').elim
  · exact heq
  · exact (key hgt h' h).elim

theorem isClassCubeG_iff {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) (sites : Set (PeriodicLatticeSite L)) (j : ℕ) :
    IsClassCubeG ell M f k S sites j ↔ 10 ≤ f ∧ DescribedAt ell M f k S sites j :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun _ _ hi => describedAt_index_unique hmono hi h.2⟩⟩

theorem isClassCube_iff {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) (sites : Set (PeriodicLatticeSite L)) (j : ℕ) :
    IsClassCube ell M f k S sites j ↔ DescribedAt ell M f k S sites j :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hi => describedAt_index_unique hmono hi h⟩⟩

theorem isClassCube_toG {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) (hf : 10 ≤ f) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (h : IsClassCube ell M f k S sites j) : IsClassCubeG ell M f k S sites j :=
  (isClassCubeG_iff hmono sites j).2 ⟨hf, h.1⟩

/-! ## 3. the general class versus r8's fixed-factor class -/

/-- the general class at bound `F` gives r8's class at every factor `f ∈ [10, F]` (in particular `f = 12`). -/
theorem PerCubeRegularG.to2 {L : PeriodicLatticeExtent} {ell M F k f : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) (h : PerCubeRegularG ell M F k S α₀ η U) (h1 : 10 ≤ f) (h2 : f ≤ F) :
    PerCubeRegular2 ell M f k S α₀ η U :=
  fun sites j hq => h f sites j h2 (isClassCube_toG hmono h1 hq)

/-- on monotone towers the general class IS r2's `PerCubeRegularMix` (ZR2A, D4). -/
theorem perCubeRegularG_iff_mix {L : PeriodicLatticeExtent} {ell M F k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hmono : ∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) :
    PerCubeRegularG ell M F k S α₀ η U ↔ PerCubeRegularMix ell M F k S α₀ η U := by
  constructor
  · intro h f h1 h2
    exact h.to2 hmono h1 h2
  · intro h f sites j hf hq
    exact h f hq.1 hf sites j ((isClassCube_iff hmono sites j).2 hq.2.1)

/-- a larger bound `F'` reads more cubes: `PerCubeRegularG F'` implies `PerCubeRegularG F` for `F ≤ F'`. -/
theorem PerCubeRegularG.mono {L : PeriodicLatticeExtent} {ell M F F' k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : PerCubeRegularG ell M F' k S α₀ η U) (hFF : F ≤ F') : PerCubeRegularG ell M F k S α₀ η U :=
  fun f sites j hf hq => h f sites j (hf.trans hFF) hq

/-- the smallest bound is the strongest headline: `P428Target8G F → P428Target8G F'` for `F ≤ F'`. -/
theorem P428Target8G.mono {F F' : ℕ} (hFF : F ≤ F') (h : P428Target8G F) : P428Target8G F' := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR R hR'
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 hT S hS Lam hL U hU => ?_⟩
  have hMa : (0 : ℝ) ≤ ((ell ^ m : ℕ) : ℝ) * α₀ := by positivity
  have hF : (F : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    have hFr : (F : ℝ) ≤ (F' : ℝ) := by exact_mod_cast hFF
    calc (F : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = (F : ℝ) * (((ell ^ m : ℕ) : ℝ) * α₀) := by ring
      _ ≤ (F' : ℝ) * (((ell ^ m : ℕ) : ℝ) * α₀) := mul_le_mul_of_nonneg_right hFr hMa
      _ = (F' : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by ring
      _ ≤ a₀ := h2
  exact hc k hk Lu α₀ h1 hF hT S hS Lam hL U (hU.mono hFF)

/-- the coverage-free r8 headline implies the general one for every `F ≥ 12`. -/
theorem P428Target8NC.toG {F : ℕ} (hF : 12 ≤ F) (h : AdalyFormal.NoCover.P428Target8NC) : P428Target8G F := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR R hR'
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 hT S hS Lam hL U hU => ?_⟩
  have hMa : (0 : ℝ) ≤ ((ell ^ m : ℕ) : ℝ) * α₀ := by positivity
  have h12 : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    have hFr : ((12 : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF
    calc ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = ((12 : ℕ) : ℝ) * (((ell ^ m : ℕ) : ℝ) * α₀) := by ring
      _ ≤ (F : ℝ) * (((ell ^ m : ℕ) : ℝ) * α₀) := mul_le_mul_of_nonneg_right hFr hMa
      _ = (F : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by ring
      _ ≤ a₀ := h2
  exact hc k hk Lu α₀ h1 h12 hT S hS Lam hL U (hU.to2 hS.1 (by norm_num) hF)

/-- the r8 headline (with its coverage at factor 12) transfers to the general class with the same coverage, for every `F ≥ 12`. -/
theorem P428Target8.toGC {F : ℕ} (hF : 12 ≤ F) (h : P428Target8) : P428Target8GC F := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR R hR'
  refine ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 hT S hS Lam hL U hcov hU => ?_⟩
  have hMa : (0 : ℝ) ≤ ((ell ^ m : ℕ) : ℝ) * α₀ := by positivity
  have h12 : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
    have hFr : ((12 : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF
    calc ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = ((12 : ℕ) : ℝ) * (((ell ^ m : ℕ) : ℝ) * α₀) := by ring
      _ ≤ (F : ℝ) * (((ell ^ m : ℕ) : ℝ) * α₀) := mul_le_mul_of_nonneg_right hFr hMa
      _ = (F : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ := by ring
      _ ≤ a₀ := h2
  exact hc k hk Lu α₀ h1 h12 hT S hS Lam hL U ⟨hcov, hU.to2 hS.1 (by norm_num) hF⟩

/-- **the general class WITH factor-12 coverage, unconditionally** (from the proved r8 headline `p428Target8`). -/
theorem p428Target8GC {F : ℕ} (hF : 12 ≤ F) : P428Target8GC F :=
  P428Target8.toGC hF AdalyFormal.M2RightInv.p428Target8

/-! ## 4. the non-box superset contains every general class cube -/

theorem siteBox_mono {L : PeriodicLatticeExtent} (z : PeriodicLatticeSite L) {s t : ℕ} (h : s ≤ t) :
    siteBox z s ⊆ siteBox z t := fun _ hx μ => lt_of_lt_of_le (hx μ) h

theorem two_blocks_aux (N z s : ℕ) (hs : 0 < s) (h2 : 2 * s ≤ N) (hz : z < N) :
    ((z + s) % N + N - z) % N = s ∧ (z + s) % N / s ≠ z / s := by
  by_cases hc : z + s < N
  · rw [Nat.mod_eq_of_lt hc]
    refine ⟨?_, ?_⟩
    · rw [show z + s + N - z = s + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.add_div_right _ hs]; omega
  · have e : (z + s) % N = z + s - N := by
      rw [show z + s = (z + s - N) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e]
    refine ⟨?_, ?_⟩
    · rw [show z + s - N + N - z = s by omega, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.div_eq_of_lt (by omega)]
      have : 1 ≤ z / s := (Nat.le_div_iff_mul_le hs).2 (by omega)
      omega

/-- a general class cube of factor `f ≤ F` is in the non-box superset (needs two level-`j` blocks along direction 0). -/
theorem isClassCubeG_toW {L : PeriodicLatticeExtent} {ell M f F k : ℕ} {S : Tower L}
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (h : IsClassCubeG ell M f k S sites j) (hfF : f ≤ F)
    (hs : 0 < bigSide M ell j) (h2 : 2 * bigSide M ell j ≤ L 0 + 1) : IsClassSetW ell M F k S sites j := by
  obtain ⟨hf, ⟨hj, ⟨z, -, rfl⟩, hsub, hne⟩, -⟩ := h
  refine ⟨hj, hsub, hne, ⟨z, siteBox_mono z (Nat.mul_le_mul_right _ hfF)⟩, ?_⟩
  set s := bigSide M ell j
  have hz0 := (z 0).isLt
  obtain ⟨hA, hB⟩ := two_blocks_aux (L 0 + 1) (z 0).val s hs h2 hz0
  have hlt : ((z 0).val + s) % (L 0 + 1) < L 0 + 1 := Nat.mod_lt _ (by omega)
  let z' : PeriodicLatticeSite L := Function.update z 0 ⟨((z 0).val + s) % (L 0 + 1), hlt⟩
  have hfs : s ≤ f * s := Nat.le_mul_of_pos_left s (by omega)
  have h2s : 2 * s ≤ f * s := Nat.mul_le_mul_right s (by omega)
  have hpos : 0 < f * s := lt_of_lt_of_le hs hfs
  have self0 : ∀ μ : Fin 3, ((z μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) = 0 := by
    intro μ
    rw [show (z μ).val + (L μ + 1) - (z μ).val = L μ + 1 by omega, Nat.mod_self]
  refine ⟨z, fun μ => by rw [self0 μ]; exact hpos, z', fun μ => ?_, 0, ?_⟩
  · by_cases hμ : μ = 0
    · subst hμ
      simp only [z', Function.update_self]
      rw [hA]; omega
    · simp only [z', Function.update_of_ne hμ]
      rw [self0 μ]; exact hpos
  · simp only [z', Function.update_self]
    exact fun h => hB h.symm

/-! ## 5. what the general class does not read -/

/-- the general class reads `U` only on bonds of general class cubes. -/
theorem perCubeG_update {L : PeriodicLatticeExtent} {ell M F k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : PerCubeRegularG ell M F k S α₀ η U) (b : Bond L)
    (hb : ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), f ≤ F → IsClassCubeG ell M f k S sites j → b.1 ∉ sites)
    (v : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    PerCubeRegularG ell M F k S α₀ η (Function.update U b v) := by
  intro f sites j hf hq
  obtain ⟨g, A, h1, h2, h3⟩ := h f sites j hf hq
  refine ⟨g, A, fun e he => ?_, h2, h3⟩
  have hne : e ≠ b := by
    intro heq
    exact hb f sites j hf hq (heq ▸ he.1)
  have : periodicGaugeTransform g (Function.update U b v) e = periodicGaugeTransform g U e := by
    simp only [periodicGaugeTransform, Function.update_of_ne hne]
  rw [this]
  exact h1 e he

/-- the constant configuration `1` is in the general class. -/
theorem perCubeG_one {L : PeriodicLatticeExtent} {ell M F k : ℕ} {S : Tower L} {α₀ η : ℝ}
    (hell : 0 < ell) (hM : 0 < M) (hα : 0 < α₀) (hη : 0 < η) :
    PerCubeRegularG ell M F k S α₀ η (fun _ => 1) := by
  intro f sites j _ hq
  have hf : 0 < f := by have := hq.1; omega
  refine ⟨fun _ => 1, fun _ => 0, fun e _ => ⟨?_, ?_, ?_⟩, fun μ ν x _ _ => ?_, fun μ x _ => ?_⟩
  · simp [HT]
  · simp [periodicGaugeTransform]
  · rw [AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    exact AdalyFormal.NoCover.classBound_pos hell hM hf hα hη j 1
  · simp only [sub_self, smul_zero, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    exact AdalyFormal.NoCover.classBound_pos hell hM hf hα hη j 2
  · rw [AdalyFormal.NoCover.ddA_zero, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    exact AdalyFormal.NoCover.classBound_pos hell hM hf hα hη j 3

#print axioms perCubeRegular2_iff
#print axioms describedAt_index_unique
#print axioms isClassCubeG_iff
#print axioms isClassCube_iff
#print axioms PerCubeRegularG.to2
#print axioms perCubeRegularG_iff_mix
#print axioms P428Target8NC.toG
#print axioms P428Target8.toGC
#print axioms p428Target8GC
#print axioms isClassCubeG_toW
#print axioms perCubeG_update
#print axioms perCubeG_one
#print axioms PerCubeRegularG.mono
#print axioms P428Target8G.mono

end AdalyFormal.GeneralClass
