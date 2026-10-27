import AU_XSV4
import AU_XSV3b
import ZT5A

/-!
# AU_XFinal -- the cube factor `c >= 10` AFTER the thresholds AND after `a0` (lane allc_20261016, uniform-in-c route)

STATEMENTS (frozen objects of ZT5A reused unchanged: `CoercG8AtWD`, `CoercG8At`, `SidePow6`, `P428Core8At`, `P428Genuine8AllC`, `P428Target8`):

* `P428Target8MaxAllC` : `forall ell >= 2, a > 0`, `exists gamma0 > 0` (depends on `ell, a` only), `exists m0 >= 1`, `forall m >= m0`, `exists R0`, `forall R >= R0`: `SidePow6 ell (ell^m) a` and
  `exists a0 > 0`, `forall c >= 10`, `forall k >= 1, Lu, alpha0 > 0` with `c * ell^m * alpha0 <= a0`: `CoercG8AtWD ell (ell^m) R k .. a Lu c alpha0 gamma0` (`WellDefG` and the printed inequality).
  Order of choices: `gamma0`, `m0`, `R0`, `a0`, then `c`.  Strictly stronger than `AU_Final.P428Target8StrongAllC` (there `a0` is chosen after `c`).
* `P428Target8AllCCopyX` : text copy of SVS `P428Target8AllC` (thresholds `m0`, `R0` before `c`); `P428Target8StrongCUX` : text copy of `AC_Final.P428Target8StrongC` (`c` first).
  Consequences: `.toAllC`, `.toStrongC`, `P428Target8AllCCopyX.toTarget : P428Target8`.
Nothing in this file proves the lemma beyond the cited theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

/-- copy of SVS `P428Target8AllC` -/
def P428Target8AllCCopyX : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8AllC ell (ell ^ m) R (by omega) a

/-- **strongest form**: `gamma0`, thresholds `m0`, `R0` and the smallness `a0` all before `c`; `WellDefG` and the inequality. -/
def P428Target8MaxAllC : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ c : ℕ, 10 ≤ c →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu c α₀ γ₀

/-- text copy of `AC_Final.P428Target8StrongC` (c fixed first). -/
def P428Target8StrongCUX : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ∀ c : ℕ, 10 ≤ c →
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu c α₀ γ₀

theorem P428Target8MaxAllC.toAllC (h : P428Target8MaxAllC) : P428Target8AllCCopyX := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, hc⟩ := hR R hR'
  refine ⟨hs, fun c hc10 => ?_⟩
  exact ⟨a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 => (hc c hc10 k hk Lu α₀ h1 h2).toHead⟩

theorem P428Target8AllCCopyX.toTarget (h : P428Target8AllCCopyX) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, h⟩ := h ell hell a ha
  exact ⟨m₀, hm₀, fun m hm => by
    obtain ⟨R₀, hR⟩ := h m hm
    exact ⟨R₀, fun R hR' => (hR R hR').toHead⟩⟩

/-- c fixed first (`P428Target8StrongC`) follows. -/
theorem P428Target8MaxAllC.toStrongC (h : P428Target8MaxAllC) : P428Target8StrongCUX := by
  intro ell hell a ha c hc
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := h ell hell a ha
  refine ⟨γ₀, hγ, m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, hh⟩ := hR R hR'
  exact ⟨hs, a₀, ha₀, hh c hc⟩

theorem fieldsX :
    (∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsK0X ell (by omega) a) ∧ OpLayerThick0X ∧ ClassRightInv0X := by
  have hRI : ClassRightInv0X := classRightInv0X_of_cov ballChartsGX classRightInvCov0X
  exact ⟨fun _ hell a ha => fieldsK0X_of_ball (ballChartsX_of_G ballChartsGX) hell a ha,
    opLayerThick0X_of ballChartsGX hRI, hRI⟩

/-- **`P428Target8MaxAllC` holds**: thresholds `m0`, `R0` before the cube factor `c >= 10`; `gamma0` before everything; `WellDefG` and the printed inequality. -/
theorem p428Target8MaxAllC : P428Target8MaxAllC := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, h⟩ := strong_coreXC fieldsX.1 fieldsX.2.1 fieldsX.2.2 hell (by omega) ha
  refine ⟨γ₀, hγ, m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := h m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨a₀, ha₀, hc'⟩ := hR R hR'
  refine ⟨⟨hell, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀, fun c hc k hk Lu α₀ hα h2 hT S hS Lam hL U hU => ?_⟩
  obtain ⟨hI, hW⟩ := hc' c hc k hk Lu α₀ hα h2 hT S hS Lam hL U hU
  exact ⟨hW, hI⟩

theorem p428Target8AllCX : P428Target8AllCCopyX := p428Target8MaxAllC.toAllC

theorem p428Target8StrongC_fromMaxAllC : P428Target8StrongCUX := p428Target8MaxAllC.toStrongC

theorem p428Target8_fromMaxAllC : P428Target8 := p428Target8AllCX.toTarget

end AdalyFormal.AllC

#print axioms AdalyFormal.AllC.fieldsX
#print axioms AdalyFormal.AllC.p428Target8MaxAllC
#print axioms AdalyFormal.AllC.p428Target8AllCX
#print axioms AdalyFormal.AllC.p428Target8StrongC_fromMaxAllC
#print axioms AdalyFormal.AllC.p428Target8_fromMaxAllC
