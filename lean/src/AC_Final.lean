import AC_SV4
import AC_SV3b
import ZT5A

/-!
# AC_Final -- the cube factor `c >= 10` fixed FIRST (lane allc_20261016)

STATEMENTS (frozen objects of ZT5A reused unchanged: `CoercG8AtWD`, `CoercG8At`, `SidePow6`, `P428Core8At`, `P428Target8`):

* `P428Target8StrongC` : `forall ell >= 2, a > 0, forall c >= 10 (a natural number, fixed first)`, `exists gamma0 > 0` (before `m`, `R`), `exists m0`, `forall m >= m0`,
  `exists R0`, `forall R >= R0`: `SidePow6 ell (ell^m) a` and `exists a0 > 0`, `forall k >= 1, Lu, alpha0 > 0` with `c * ell^m * alpha0 <= a0`:
  `CoercG8AtWD ell (ell^m) R k .. a Lu c alpha0 gamma0` (conclusion `WellDefG` and the printed inequality, class cube factor `c`).
  `m0, R0` MAY depend on `c`; `a0` on `(ell, a, c, m, R)`; `gamma0` on `(ell, a, c)`.
* `P428Target8AllCle12` : ZT5A `P428Genuine8AllC` (thresholds `m0`, `R0` BEFORE `c`) restricted to `10 <= c <= 12`.
* `StrongC12` : the instance `c = 12` equals `P428Target8Strong` (lane strong_variants, text copy `P428Target8StrongCopy`).
Nothing in this file proves the lemma beyond the cited theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

/-- copy of SVS `P428Core8WDg` (γ₀ supplied from outside) -/
def P428Core8WDgCopy (ell M R : ℕ) (hell : 0 < ell) (a γ₀ : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtWD ell M R k hell a Lu 12 α₀ γ₀

/-- copy of SVS `P428Target8Strong` -/
def P428Target8StrongCopy : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ P428Core8WDgCopy ell (ell ^ m) R (by omega) a γ₀

/-- **the cube factor `c ≥ 10` fixed first, `WellDefG` ∧ inequality, `γ₀` before `m, R`.** -/
def P428Target8StrongC : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∀ c : ℕ, 10 ≤ c →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu c α₀ γ₀

/-- ZT5A `P428Genuine8AllC` (the thresholds `m₀`, `R₀` are chosen BEFORE `c`) restricted to `10 ≤ c ≤ 12`. -/
def P428Target8AllCle12 : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∀ c : ℕ, 10 ≤ c → c ≤ 12 → P428Core8At ell (ell ^ m) R (by omega) a c

/-- ZT5A `P428Genuine8AllC` (thresholds `m₀`, `R₀` BEFORE `c`) restricted to the finite range `10 ≤ c ≤ B`; `m₀, R₀` may depend on `B`. -/
def P428Target8AllCleB (B : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∀ c : ℕ, 10 ≤ c → c ≤ B → P428Core8At ell (ell ^ m) R (by omega) a c

/-! ## implications -/

theorem P428Target8StrongC.toStrong (h : P428Target8StrongC) : P428Target8StrongCopy := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := h ell hell a ha 12 (by norm_num)
  refine ⟨γ₀, hγ, m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, hc⟩ := hR R hR'
  exact ⟨hs, a₀, ha₀, fun k hk Lu α₀ h1 h2 => hc k hk Lu α₀ h1 (by simpa using h2)⟩

theorem P428Target8StrongCopy.toTarget (h : P428Target8StrongCopy) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, hc⟩ := hR R hR'
  exact ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 => (hc k hk Lu α₀ h1 h2).toHead⟩

/-- the thresholds of finitely many cube factors can be merged: `10, 11, 12`. -/
theorem P428Target8StrongC.toAllCle12 (h : P428Target8StrongC) : P428Target8AllCle12 := by
  intro ell hell a ha
  obtain ⟨γ10, hγ10, m10, hm10, h10⟩ := h ell hell a ha 10 le_rfl
  obtain ⟨γ11, hγ11, m11, hm11, h11⟩ := h ell hell a ha 11 (by norm_num)
  obtain ⟨γ12, hγ12, m12, hm12, h12⟩ := h ell hell a ha 12 (by norm_num)
  refine ⟨max (max m10 m11) m12, by omega, fun m hm => ?_⟩
  obtain ⟨R10, hR10⟩ := h10 m (by omega)
  obtain ⟨R11, hR11⟩ := h11 m (by omega)
  obtain ⟨R12, hR12⟩ := h12 m (by omega)
  refine ⟨max (max R10 R11) R12, fun R hR => ?_⟩
  obtain ⟨hs, -⟩ := hR10 R (by omega)
  refine ⟨hs, fun c hc1 hc2 => ?_⟩
  have hc : c = 10 ∨ c = 11 ∨ c = 12 := by omega
  rcases hc with rfl | rfl | rfl
  · obtain ⟨-, a₀, ha₀, hc⟩ := hR10 R (by omega)
    exact ⟨a₀, ha₀, γ10, hγ10, fun k hk Lu α₀ h1 h2 => (hc k hk Lu α₀ h1 h2).toHead⟩
  · obtain ⟨-, a₀, ha₀, hc⟩ := hR11 R (by omega)
    exact ⟨a₀, ha₀, γ11, hγ11, fun k hk Lu α₀ h1 h2 => (hc k hk Lu α₀ h1 h2).toHead⟩
  · obtain ⟨-, a₀, ha₀, hc⟩ := hR12 R (by omega)
    exact ⟨a₀, ha₀, γ12, hγ12, fun k hk Lu α₀ h1 h2 => (hc k hk Lu α₀ h1 h2).toHead⟩

/-- the thresholds of finitely many cube factors can be merged: every finite range `10 ≤ c ≤ B`. -/
theorem P428Target8StrongC.toAllCleB (h : P428Target8StrongC) (B : ℕ) : P428Target8AllCleB B := by
  classical
  intro ell hell a ha
  have h1 : ∀ c : ℕ, 10 ≤ c → ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu c α₀ γ₀ := fun c hc => h ell hell a ha c hc
  choose! γ hγ m₀ hm₀ hmain using h1
  refine ⟨Finset.sup (Finset.Icc 10 B) m₀ + 1, by omega, fun m hm => ?_⟩
  have hmc : ∀ c : ℕ, 10 ≤ c → c ≤ B → m₀ c ≤ m := fun c hc1 hc2 =>
    le_trans (Finset.le_sup (f := m₀) (Finset.mem_Icc.mpr ⟨hc1, hc2⟩)) (by omega)
  have h2 : ∀ c : ℕ, ∃ R₀ : ℕ, 10 ≤ c → c ≤ B → ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu c α₀ (γ c) := by
    intro c
    by_cases hc : 10 ≤ c ∧ c ≤ B
    · obtain ⟨R₀, hR⟩ := hmain c hc.1 m (hmc c hc.1 hc.2)
      exact ⟨R₀, fun _ _ R hR' => hR R hR'⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose R₀ hR₀ using h2
  refine ⟨Finset.sup (Finset.range (B + 1)) R₀, fun R hR => ?_⟩
  have hRc : ∀ c : ℕ, 10 ≤ c → c ≤ B → R₀ c ≤ R := fun c hc1 hc2 =>
    le_trans (Finset.le_sup (f := R₀) (Finset.mem_range.mpr (by omega))) hR
  have hS : SidePow6 ell (ell ^ m) a := by
    by_cases hB : 10 ≤ B
    · exact (hR₀ 10 le_rfl hB R (hRc 10 le_rfl hB)).1
    · exact ⟨hell, ⟨m, by omega, rfl⟩, ha⟩
  refine ⟨hS, fun c hc1 hc2 => ?_⟩
  obtain ⟨-, a₀, ha₀, hc⟩ := hR₀ c hc1 hc2 R (hRc c hc1 hc2)
  exact ⟨a₀, ha₀, γ c, hγ c hc1, fun k hk Lu α₀ h1 h2 => (hc k hk Lu α₀ h1 h2).toHead⟩

/-! ## the proof: the three field inputs at cube factor `c`, then `strong_coreAC` -/

theorem fields0 (c : ℕ) [CubeFactor c] :
    (∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsK0 ell c (by omega) a) ∧ OpLayerThick0 c ∧ ClassRightInv0 c :=
  ⟨fun _ hell a ha => fieldsK0_of_ball (ballCharts0_of_G ballChartsG0) hell a ha,
    opLayerThick0_of ballChartsG0 (classRightInv0_of_cov ballChartsG0 classRightInvCov0),
    classRightInv0_of_cov ballChartsG0 classRightInvCov0⟩

/-- **`P428Target8StrongC` holds**: every cube factor `c ≥ 10`, `WellDefG` ∧ the printed inequality, `γ₀` before `m, R`. -/
theorem p428Target8StrongC : P428Target8StrongC := by
  intro ell hell a ha c hc
  haveI : CubeFactor c := ⟨hc⟩
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := strong_coreAC (fc := c) (fields0 c).1 (fields0 c).2.1 (fields0 c).2.2 hell (by omega) ha
  refine ⟨γ₀, hγ, m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨a₀, ha₀, hc'⟩ := hR R hR'
  refine ⟨⟨hell, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀, fun k hk Lu α₀ hα h2 hT S hS Lam hL U hU => ?_⟩
  obtain ⟨hI, hW⟩ := hc' k hk Lu α₀ hα h2 hT S hS Lam hL U hU
  exact ⟨hW, hI⟩

theorem p428Target8AllCle12 : P428Target8AllCle12 := p428Target8StrongC.toAllCle12

theorem p428Target8AllCleB (B : ℕ) : P428Target8AllCleB B := p428Target8StrongC.toAllCleB B

theorem p428Target8_fromStrongC : P428Target8 := p428Target8StrongC.toStrong.toTarget

end AdalyFormal.AllC

#print axioms AdalyFormal.AllC.fields0
#print axioms AdalyFormal.AllC.p428Target8StrongC
#print axioms AdalyFormal.AllC.p428Target8AllCle12
#print axioms AdalyFormal.AllC.p428Target8AllCleB
#print axioms AdalyFormal.AllC.p428Target8_fromStrongC
