import MC1b

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-!
# MC2 -- the M0 statement and `M0Core_of_headline`: M0 is a CONSEQUENCE of the frozen headline `P428Genuine8`.
`GlobalRegular2` = the printed class (3.35)+(3.36) with ONE gauge `g` and ONE `A` on the whole torus; same three clauses, same constants as
`PerCubeRegular2 .. c ..` at index j = k.
-/
namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- (3.35)+(3.36) with a single global gauge: the three clauses of `PerCubeRegular2` at `j = k`, without the cube guards. -/
def GlobalRegular2 {L : PeriodicLatticeExtent} (ell M f k : ℕ) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ e : Bond L, HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 1)) ∧
    (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 2)) ∧
    (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        frobNorm (ddA η A x μ) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 3))

/-- on the full tower the only class cubes have index `k` -/
theorem fullTower_classCube_index {ell M f k : ℕ} {Lu : PeriodicLatticeExtent}
    {sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))} {j : ℕ}
    (h : IsClassCube ell M f k (fullTower ell k Lu) sites j) : j = k := by
  obtain ⟨⟨hjk, _, _, y, hy1, hy2⟩, _⟩ := h
  by_contra hne
  have hlt : j < k := lt_of_le_of_ne hjk hne
  have h1 : j ≤ k := hjk
  have h2 : j + 1 ≤ k := by omega
  simp [towerBj, fullTower, h1, h2] at hy2

/-- **`perCube_of_global`**: a global-gauge configuration is in the per-cube class (pure restriction). -/
theorem perCube_of_global {ell M f k : ℕ} {Lu : PeriodicLatticeExtent} {α₀ η : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (h : GlobalRegular2 ell M f k α₀ η U) :
    PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ η U := by
  obtain ⟨g, A, h1, h2, h3⟩ := h
  intro sites j hq
  have hj := fullTower_classCube_index hq
  subst hj
  exact ⟨g, A, fun e _ => h1 e, fun μ ν x _ _ => h2 μ ν x, fun μ x _ => h3 μ x⟩

/-- the class hypothesis of the headline at `(fullTower, ·)` follows from `GlobalRegular2`. -/
theorem classCoupled_of_global {ell M f k : ℕ} (hell : 0 < ell) (hM : 0 < M) (hf : 2 ≤ f)
    {Lu : PeriodicLatticeExtent} (hT : ∀ μ : Fin 3, M ∣ Lu μ + 1) {α₀ η : ℝ}
    {U : LinkCfg (scaleUp ell k Lu)} (h : GlobalRegular2 ell M f k α₀ η U) :
    ClassCoupled ell M f k (fullTower ell k Lu) α₀ η U :=
  ⟨fullTower_coversp ell M f k hell hM hf Lu hT, perCube_of_global h⟩

/-- **M0 inner claim** (ell, M, a fixed by the consumer, exactly as in the headline; `Λ = ` whole torus, full tower). -/
def M0Core (ell M : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent), TorusOK ell M Lu →
    ∀ (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), GlobalRegular2 ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ U →
      InstIneq ell k hell a Lu γ₀ (fullTower ell k Lu) Set.univ U

def M0Target : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → M0Core ell (ell ^ m) (by omega) a

/-- **M0 is a consequence of the frozen headline.** -/
theorem M0Core_of_headline {ell M R : ℕ} {hell : 0 < ell} {a : ℝ}
    (h : P428Genuine8 ell M R hell a) : M0Core ell M hell a := by
  obtain ⟨hside, a₀, ha₀, γ₀, hγ₀, hall⟩ := h
  have hMpos : 0 < M := hside.toDvd.2.1
  refine ⟨a₀, ha₀, γ₀, hγ₀, fun k hk Lu hT α₀ hα hsm U hU => ?_⟩
  exact hall k hk Lu α₀ hα hsm hT (fullTower ell k Lu) (fullTower_admissible ell M R k hell hk Lu hT.2.2)
    Set.univ (univ_lambdaOK2 ell M R k hell Lu) U (classCoupled_of_global hell hMpos (by norm_num) hT.2.2 hU)

theorem M0Target_of_target (h : P428Target8) : M0Target := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  exact M0Core_of_headline (hR R₀ le_rfl)

/-- **(r8 transfer) the r8 locality room is available at the headline's own `R`.**  r8's locality theorems
(`genForm_congr_outside`, `InstIneq_congr_class`, ZR8Data/ZR8Class) carry the room hypothesis `17 * ell ≤ R * M`; the
headline `P428Target8` quantifies `∀ R ≥ R₀`, so at every admissible `m` there is an `R` with the room AND the headline
at that `R`; `M0Core` follows from the headline at that same `R` (`M0Core_of_headline` itself uses no locality and holds
for every `R`). -/
theorem headline_at_room (h : P428Target8) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ R : ℕ, 17 * ell ≤ R * ell ^ m ∧ P428Genuine8 ell (ell ^ m) R (by omega) a ∧
        M0Core ell (ell ^ m) (by omega) a := by
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  have hpos : 1 ≤ ell ^ m := Nat.one_le_pow _ _ (by omega)
  have hG := hR (max R₀ (17 * ell)) (le_max_left _ _)
  refine ⟨max R₀ (17 * ell), ?_, hG, M0Core_of_headline hG⟩
  calc 17 * ell ≤ max R₀ (17 * ell) := le_max_right _ _
    _ = max R₀ (17 * ell) * 1 := (mul_one _).symm
    _ ≤ max R₀ (17 * ell) * ell ^ m := Nat.mul_le_mul_left _ hpos

#print axioms headline_at_room
#print axioms perCube_of_global
#print axioms classCoupled_of_global
#print axioms M0Core_of_headline
#print axioms M0Target_of_target

end AdalyFormal.M0Corollary
