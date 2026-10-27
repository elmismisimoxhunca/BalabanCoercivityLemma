import ZT5A

/-!
# NC1 -- `P428Target8NC`: the frozen r8 headline WITHOUT the coverage hypothesis (lane nocover_20261015)

Text of `ZT5A.CoercG8At`/`P428Core8At`/`P428Core8`/`P428Genuine8`/`P428Target8`, copied verbatim, with ONE change:
the class hypothesis

    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U          -- r8 (ZR6A: CoversOm0p ell M c k S ∧ PerCubeRegular2 ...)

is replaced by

    PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U        -- NC (ZR2A: (3.35)+(3.36) on every class cube)

i.e. the tower-only conjunct `CoversOm0p ell M c k S` (ZR6A:33, not printed) is dropped.  Nothing else changes: same binders,
same order, same `TorusOK`, `Admissible`, `LambdaOK2`, same conclusion `InstIneq`, same constants block (`c = 12`), same side
condition `SidePow6`, same outer thresholds.
CMP99b p.396: "these regularity conditions do not impose any constraints on U outside the domain Ω₀."  Coverage is not printed.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.NoCover

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- `CoercG8At` with `ClassCoupled` replaced by `PerCubeRegular2` (no coverage). -/
def CoercG8AtNC (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

/-- `P428Core8At` over `CoercG8AtNC`. -/
def P428Core8AtNC (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtNC ell M R k hell a Lu c α₀ γ₀

/-- the headline constants block, `c = 12`. -/
def P428Core8NC (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop := P428Core8AtNC ell M R hell a 12

/-- `P428Genuine8` over `P428Core8NC` (printed side condition `M = ell^m`). -/
def P428Genuine8NC (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8NC ell M R hell a

/-- **`P428Target8NC`**: the r8 headline `P428Target8` with the coverage conjunct removed from the class hypothesis. -/
def P428Target8NC : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8NC ell (ell ^ m) R (by omega) a

/-- pin: the NC inner claim is the r8 inner claim with `PerCubeRegular2` in the class slot. -/
theorem coercNC_unfold (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (c : ℕ) (α₀ γ₀ : ℝ) :
    CoercG8AtNC ell M R k hell a Lu c α₀ γ₀ ↔
      (TorusOK ell M Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          InstIneq ell k hell a Lu γ₀ S Lam U) := Iff.rfl

/-- NC is (weakly) STRONGER than r8: `ClassCoupled = CoversOm0p ∧ PerCubeRegular2` gives the NC hypothesis. -/
theorem CoercG8AtNC.toR8 {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {c : ℕ} {α₀ γ₀ : ℝ}
    (h : CoercG8AtNC ell M R k hell a Lu c α₀ γ₀) : CoercG8At ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => h hT S hS Lam hL U hU.2

theorem P428Target8NC.toTarget (h : P428Target8NC) : P428Target8 := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm' => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hm'
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨hs, a₀, ha₀, γ₀, hγ, hc⟩ := hR R hR'
  exact ⟨hs, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ h1 h2 => (hc k hk Lu α₀ h1 h2).toR8⟩

#print axioms coercNC_unfold
#print axioms CoercG8AtNC.toR8
#print axioms P428Target8NC.toTarget

end AdalyFormal.NoCover
