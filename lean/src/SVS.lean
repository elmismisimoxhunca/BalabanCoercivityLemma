import ZT5A

/-!
# SVS -- STATEMENTS of the strong variants (lane strong_variants_20261016).  NOTHING HERE PROVES THE LEMMA.

Every definition reuses the frozen r8 objects of `ZT5A` (`CoercG8At`, `CoercG8AtWD`, `P428Genuine8WD`, `P428Genuine8AllC`, `SidePow6`) unchanged;
only the outer quantifier order / the choice of conclusion changes.  The mechanical diff against `ZT5A` is `STATEMENT_DIFF.txt`.

* `P428Target8WD`     : the ZT5A variant `P428Genuine8WD` (conclusion `WellDefG ∧` inequality) at the headline's outer quantification.
* `P428Target8G0`     : the headline with `γ₀` chosen BEFORE `m` and `R` (`a₀` may still depend on `m, R`).
* `P428Target8Strong` : both: `WellDefG ∧` inequality, `γ₀` chosen before `m, R`.
* `P428Target8AllC`   : the ZT5A variant `P428Genuine8AllC` (every cube factor `c ≥ 10`) at the headline's outer quantification.
* `P428Target8Max`    : WD + every `c ≥ 10` fixed FIRST + `a₀, γ₀` uniform in `M, R` (combination of the three ZT5A variants).
-/
set_option autoImplicit false

namespace AdalyFormal.StrongVariants

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

/-- `P428Core8WD` with `γ₀` supplied from outside. -/
def P428Core8WDg (ell M R : ℕ) (hell : 0 < ell) (a γ₀ : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtWD ell M R k hell a Lu 12 α₀ γ₀

/-- `P428Core8At` with `γ₀` supplied from outside. -/
def P428Core8Atg (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) (γ₀ : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8At ell M R k hell a Lu c α₀ γ₀

/-- the WD variant (`ZT5A.P428Genuine8WD`) at the headline's outer quantification. -/
def P428Target8WD : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8WD ell (ell ^ m) R (by omega) a

/-- the headline with `γ₀` chosen before `m, R`. -/
def P428Target8G0 : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ P428Core8Atg ell (ell ^ m) R (by omega) a 12 γ₀

/-- **STRONG**: conclusion `WellDefG ∧` the printed inequality (`CoercG8AtWD`), `γ₀` chosen before `m, R`. -/
def P428Target8Strong : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ P428Core8WDg ell (ell ^ m) R (by omega) a γ₀

/-- the AllC variant (`ZT5A.P428Genuine8AllC`) at the headline's outer quantification. -/
def P428Target8AllC : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8AllC ell (ell ^ m) R (by omega) a

/-- **MAX** (WD + AllC + Unif): `c ≥ 10` fixed FIRST (after `ell, a`), then thresholds and `a₀, γ₀` (depending on `ell, a, c` only),
uniform over `m ≥ m₁`, `R ≥ R₁`; conclusion `WellDefG ∧` inequality at cube factor `c`, smallness `c M α₀ ≤ a₀`. -/
def P428Target8Max : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∀ c : ℕ, 10 ≤ c →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu c α₀ γ₀

/-! ## implications -/

theorem P428Target8WD.toTarget (h : P428Target8WD) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, h⟩ := h ell hell a ha
  exact ⟨m₀, hm₀, fun m hm => by
    obtain ⟨R₀, hR⟩ := h m hm
    exact ⟨R₀, fun R hR' => (hR R hR').toHead⟩⟩

theorem P428Target8G0.toTarget (h : P428Target8G0) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, hc⟩ := hR R hR'
  exact ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩

theorem P428Target8Strong.toWD (h : P428Target8Strong) : P428Target8WD := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, hc⟩ := hR R hR'
  exact ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩

theorem P428Target8Strong.toG0 (h : P428Target8Strong) : P428Target8G0 := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := h ell hell a ha
  refine ⟨γ₀, hγ, m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, hc⟩ := hR R hR'
  refine ⟨hs, a₀, ha₀, fun k hk Lu α₀ h1 h2 => (hc k hk Lu α₀ h1 (by simpa using h2)).toHead⟩

theorem P428Target8Strong.toTarget (h : P428Target8Strong) : P428Target8 := h.toWD.toTarget

/-- the ZT5A `Unif` variant implies `G0`. -/
theorem P428Target8Unif.toG0 (h : P428Target8Unif) : P428Target8G0 := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hU⟩ := h ell hell a ha
  refine ⟨γ₀, hγ, m₁, hm₁, fun m hm => ⟨R₁, fun R hR => ?_⟩⟩
  refine ⟨⟨hell, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀, fun k hk Lu α₀ h1 h2 => ?_⟩
  exact hU m hm R hR k hk Lu α₀ h1 (by simpa using h2)

theorem P428Target8AllC.toTarget (h : P428Target8AllC) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, h⟩ := h ell hell a ha
  exact ⟨m₀, hm₀, fun m hm => by
    obtain ⟨R₀, hR⟩ := h m hm
    exact ⟨R₀, fun R hR' => (hR R hR').toHead⟩⟩

/-- `Max` at `c = 12` gives `Strong`. -/
theorem P428Target8Max.toStrong (h : P428Target8Max) : P428Target8Strong := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hU⟩ := h ell hell a ha 12 (by norm_num)
  refine ⟨γ₀, hγ, m₁, hm₁, fun m hm => ⟨R₁, fun R hR => ?_⟩⟩
  refine ⟨⟨hell, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀, fun k hk Lu α₀ h1 h2 => ?_⟩
  exact hU m hm R hR k hk Lu α₀ h1 (by simpa using h2)

/-- `Max` at `c = 12` gives the ZT5A `Unif` variant. -/
theorem P428Target8Max.toUnif (h : P428Target8Max) : P428Target8Unif := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hU⟩ := h ell hell a ha 12 (by norm_num)
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ h1 h2 =>
    (hU m hm R hR k hk Lu α₀ h1 (by simpa using h2)).toHead⟩

/-- `Max` gives the ZT5A `AllC` block at every `(ell, M = ell^m, R)` beyond the `c`-DEPENDENT thresholds. -/
theorem P428Target8Max.toAllC_at (h : P428Target8Max) {ell : ℕ} (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) {c : ℕ} (hc : 10 ≤ c) :
    ∃ m₁ : ℕ, ∃ R₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → P428Core8At ell (ell ^ m) R (by omega) a c := by
  obtain ⟨m₁, -, R₁, a₀, ha₀, γ₀, hγ, hU⟩ := h ell hell a ha c hc
  exact ⟨m₁, R₁, fun m hm R hR => ⟨a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 =>
    (hU m hm R hR k hk Lu α₀ h1 (by simpa using h2)).toHead⟩⟩

end AdalyFormal.StrongVariants

#print axioms AdalyFormal.StrongVariants.P428Core8WDg
#print axioms AdalyFormal.StrongVariants.P428Core8Atg
#print axioms AdalyFormal.StrongVariants.P428Target8WD
#print axioms AdalyFormal.StrongVariants.P428Target8G0
#print axioms AdalyFormal.StrongVariants.P428Target8Strong
#print axioms AdalyFormal.StrongVariants.P428Target8AllC
#print axioms AdalyFormal.StrongVariants.P428Target8Max
#print axioms AdalyFormal.StrongVariants.P428Target8WD.toTarget
#print axioms AdalyFormal.StrongVariants.P428Target8G0.toTarget
#print axioms AdalyFormal.StrongVariants.P428Target8Strong.toWD
#print axioms AdalyFormal.StrongVariants.P428Target8Strong.toG0
#print axioms AdalyFormal.StrongVariants.P428Target8Strong.toTarget
#print axioms AdalyFormal.StrongVariants.P428Target8Unif.toG0
#print axioms AdalyFormal.StrongVariants.P428Target8AllC.toTarget
#print axioms AdalyFormal.StrongVariants.P428Target8Max.toStrong
#print axioms AdalyFormal.StrongVariants.P428Target8Max.toUnif
#print axioms AdalyFormal.StrongVariants.P428Target8Max.toAllC_at
