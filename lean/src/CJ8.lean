import CJ7
import TargetContract

/-!
# CJ8 -- the frozen r8 headline is unchanged if every quantified instance is required to be JUNK-FREE

`ReadRowsGenuineAt ell M R k Lu c α₀`: for every `TorusOK` torus, admissible tower, `Λ` with `LambdaOK2` and `U` in the class
`ClassCoupled ell M c k S α₀ (ell^{-k})`, every bond-sector row `b ∈ bondsLam j` (`1 ≤ j ≤ k`) is `Genuine` and every unit row
`CRowIn` is `C^∞` (the rows the r8 jets read).

`headline_junkfree_wlog`: `P428Target8 ↔` the same statement in which, for every covered `(ell, m, R)`, the constants block
`P428Core8` is strengthened to also deliver `ReadRowsGenuineAt` at every instance it quantifies (same `a₀`).  Direction `→`
shrinks `a₀` to `min a₀ θ(ell)` (`classSmall_exists`) and raises `R₀` to `max R₀ 17` (room `17 ell ≤ R ell^m`, `m ≥ 1`);
direction `←` forgets the extra conjunct.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ClassJets

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK CRowIn)
open AdalyFormal.StatementLane2 (ClassCoupled)
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

/-- every row read by the r8 jets is genuine, at every instance of the class with parameters `(ell, M, R, k, Lu, c, α₀)`. -/
def ReadRowsGenuineAt (ell M R k : ℕ) (hell0 : 0 < ell) (Lu : PeriodicLatticeExtent) (c : ℕ) (α₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)), ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    (∀ j, 1 ≤ j → j ≤ k → ∀ b ∈ bondsLam (geomOf ell k S) j, Genuine ell (bgTower (geomOf ell k S) U) j b) ∧
    (∀ cb : CoarseBond Lu ell, CRowIn ell Lam cb →
      ContDiffAt ℝ ⊤ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2)) 0)

/-- the constants block with the junk-free conjunct (same `a₀`, `γ₀`). -/
def P428Core8JF (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
      CoercG8At ell M R k hell a Lu 12 α₀ γ₀ ∧ ReadRowsGenuineAt ell M R k hell Lu 12 α₀

/-- the headline with the junk-free conjunct. -/
def P428Target8JF : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ P428Core8JF ell (ell ^ m) R (by omega) a

theorem room_of_R17 (ell m R : ℕ) (hell : 2 ≤ ell) (hm : 1 ≤ m) (hR : 17 ≤ R) : 17 * ell ≤ R * ell ^ m := by
  have h1 : ell ≤ ell ^ m := by
    calc ell = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ m := Nat.pow_le_pow_right (by omega) hm
  calc 17 * ell ≤ R * ell := Nat.mul_le_mul_right ell hR
    _ ≤ R * ell ^ m := Nat.mul_le_mul_left R h1

/-- **the frozen headline is unchanged by requiring every quantified instance to be junk-free.** -/
theorem headline_junkfree_wlog : P428Target8 ↔ P428Target8JF := by
  constructor
  · intro h ell hell a ha
    obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
    obtain ⟨θ, hθ, hsm⟩ := classSmall_exists ell
    refine ⟨m₀, hm₀, fun m hm' => ?_⟩
    obtain ⟨R₀, hR⟩ := hm m hm'
    refine ⟨max R₀ 17, fun R hR' => ?_⟩
    obtain ⟨hside, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R (le_trans (le_max_left _ _) hR')
    refine ⟨hside, min a₀ θ, lt_min ha₀ hθ, γ₀, hγ, fun k hk Lu α₀ hα hsmall => ⟨?_, ?_⟩⟩
    · exact hcore k hk Lu α₀ hα (le_trans hsmall (min_le_left _ _))
    · have hroom : 17 * ell ≤ R * ell ^ m := room_of_R17 ell m R hell (by omega) (le_trans (le_max_right _ _) hR')
      have hcs : ClassSmall ell (((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀) := by
        refine hsm _ ?_ ?_
        · positivity
        · push_cast; push_cast at hsmall; exact le_trans hsmall (min_le_right _ _)
      intro hT S hS Lam hLam U hU
      refine ⟨fun j hj1 hjk b hb => classRows_QlinB hell hroom hS hT hU hcs hj1 hjk hb,
        fun cb hc => classRows_unit (by omega) hell hk hroom hS hT hLam hU hcs cb hc⟩
  · intro h ell hell a ha
    obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
    refine ⟨m₀, hm₀, fun m hm' => ?_⟩
    obtain ⟨R₀, hR⟩ := hm m hm'
    refine ⟨R₀, fun R hR' => ?_⟩
    obtain ⟨hside, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R hR'
    exact ⟨hside, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα hsmall => (hcore k hk Lu α₀ hα hsmall).1⟩

#print axioms room_of_R17
#print axioms headline_junkfree_wlog

end AdalyFormal.ClassJets
