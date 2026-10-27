import TT_C
import TT_Z
import AU_XFinal

/-!
# TT_F -- **`P428Target8Total`**: the common strengthening of `P428Target8Max` and `P428Target8MaxAllC` (lane total_20261017)

`P428Target8Total` : for every `ell ≥ 2`, `a > 0`: there are `m₁ ≥ 1`, `R₁`, `a₀ > 0`, `γ₀ > 0` such that for EVERY cube factor `c ≥ 10` and every `m ≥ m₁`, `R ≥ R₁`,
`k ≥ 1`, `Lu`, `α₀ > 0` with `c · ell^m · α₀ ≤ a₀`:  `CoercG8AtWD ell (ell^m) R k _ a Lu c α₀ γ₀` (`WellDefG` and the printed inequality at class factor `c`).
All four constants are chosen before `c`, `m`, `R`.

* `p428Target8Total : P428Target8Total`  (cube-factor-free cover geometry `TT_G`, `TT_Z`; field chain `TT_B`; core `TT_C`).
* `P428Target8Total.toMax : StrongVariants.P428Target8Max`  (fix `c` first),
* `P428Target8Total.toMaxAllC : AllC.P428Target8MaxAllC`  (`γ₀`, `m₀ = m₁`, `R₀ = R₁` for every `m`, `a₀` before `c`),
* `.toAllC : StrongVariants.P428Target8AllC`, `.toTarget : StatementLaneG.P428Target8`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.AllC (CubeFactor)

/-- **the common strengthening** (`a₀`, `γ₀`, `m₁`, `R₁` before the cube factor `c ≥ 10`, and uniform over `m ≥ m₁`, `R ≥ R₁`). -/
def P428Target8Total : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          CoercG8AtWD ell (ell ^ m) R k (by omega) a Lu c α₀ γ₀

theorem fieldsT :
    (∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsKT ell (by omega) a) ∧ OpLayerThickT ∧ ClassRightInvT := by
  have hB : BallChartsGT := ballChartsGT_proved
  have hRI : ClassRightInvT := classRightInvT_of_cov hB (classRightInvCovT hB)
  exact ⟨fun _ hell a ha => fieldsKT_of_ball (ballChartsT_of_G hB) hell a ha, opLayerThickT_of hB hRI, hRI⟩

/-- **`P428Target8Total`, proved.** -/
theorem p428Target8Total : P428Target8Total := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, R₀, a₀, ha₀, hcore⟩ := strong_coreTC fieldsT.1 fieldsT.2.1 fieldsT.2.2 hell (by omega) ha
  refine ⟨m₀, hm₀, R₀, a₀, ha₀, γ₀, hγ, fun c hc m hm R hR k hk Lu α₀ hα h2 => ?_⟩
  intro hT S hS Lam hL U hU
  obtain ⟨hI, hW⟩ := hcore c hc m hm R hR k hk Lu α₀ hα h2 hT S hS Lam hL U hU
  exact ⟨hW, hI⟩

/-- `Total` ⟹ `P428Target8Max` (the cube factor fixed first). -/
theorem P428Target8Total.toMax (h : P428Target8Total) : AdalyFormal.StrongVariants.P428Target8Max := by
  intro ell hell a ha c hc
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := h ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα h2 => hT c hc m hm R hR k hk Lu α₀ hα h2⟩

/-- `Total` ⟹ `P428Target8MaxAllC` (`γ₀`, `m₀`, `R₀`, `a₀` before `c`; `R₀` independent of `m`). -/
theorem P428Target8Total.toMaxAllC (h : P428Target8Total) : AdalyFormal.AllC.P428Target8MaxAllC := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := h ell hell a ha
  refine ⟨γ₀, hγ, m₁, hm₁, fun m hm => ⟨R₁, fun R hR => ?_⟩⟩
  exact ⟨⟨hell, ⟨m, by omega, rfl⟩, ha⟩, a₀, ha₀,
    fun c hc k hk Lu α₀ hα h2 => hT c hc m hm R hR k hk Lu α₀ hα h2⟩

/-- `Total` ⟹ `P428Target8AllC` (SVS; thresholds before `c`). -/
theorem P428Target8Total.toAllC (h : P428Target8Total) : AdalyFormal.StrongVariants.P428Target8AllC :=
  h.toMaxAllC.toAllC

/-- `Total` ⟹ the frozen headline `P428Target8`. -/
theorem P428Target8Total.toTarget (h : P428Target8Total) : P428Target8 :=
  h.toAllC.toTarget

theorem p428Target8Max_fromTotal : AdalyFormal.StrongVariants.P428Target8Max := p428Target8Total.toMax
theorem p428Target8MaxAllC_fromTotal : AdalyFormal.AllC.P428Target8MaxAllC := p428Target8Total.toMaxAllC
theorem p428Target8AllC_fromTotal : AdalyFormal.StrongVariants.P428Target8AllC := p428Target8Total.toAllC
theorem p428Target8_fromTotal : P428Target8 := p428Target8Total.toTarget

end AdalyFormal.Total

#print axioms AdalyFormal.Total.ballChartsGT_proved
#print axioms AdalyFormal.Total.fieldsT
#print axioms AdalyFormal.Total.p428Target8Total
#print axioms AdalyFormal.Total.p428Target8Max_fromTotal
#print axioms AdalyFormal.Total.p428Target8MaxAllC_fromTotal
#print axioms AdalyFormal.Total.p428Target8AllC_fromTotal
#print axioms AdalyFormal.Total.p428Target8_fromTotal
