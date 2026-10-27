import R7Fork.ZGU1L

/-!
# GU1M -- MUST-FIRE: the constant mode pins the `η`-power at `U = 1` (k ≥ 1).
For the TRUE `η = ell^{-k}` the genuine form vanishes on `B_c`; every mutated power `η'` with
`η' · ell^k ≠ 1` gives a NONZERO value `(η' ell^k - 1) a ‖B_c‖²`.  At `k = 1, ell = 2` this refutes
`η²`, `1` and `η⁻¹`.   Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem genFormMut_const (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) (c : Fin 3 → SuTwo) (η' : ℝ) :
    genFormMut (PK ell k Lu hell a Lam) η' 1 (Bconst Lu c)
      = (η' * (ell : ℝ) ^ k - 1) * a * ‖Bconst Lu c‖ ^ 2 := by
  have hJ : (PK ell k Lu hell a Lam).Jf = 0 := Jf_flat _ rfl
  unfold genFormMut firstTermMut
  rw [hJ, inner_zero_right, real_inner_self_eq_norm_sq]
  rw [constMode_firstTerm ell k Lu hell a Lam hN ha c]
  show η' * (a * (ell : ℝ) ^ k * ‖Bconst Lu c‖ ^ 2) - a * ‖Bconst Lu c‖ ^ 2 - 2 * 1 * 0 = _
  ring

/-- the genuine form vanishes on the constant mode at every `k` -/
theorem genForm_const_zero (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hN : ∀ μ, 1 ≤ Lu μ) (ha : 0 < a) (c : Fin 3 → SuTwo) :
    GenP.genForm (PK ell k Lu hell a Lam) (Bconst Lu c) = 0 := by
  rw [← genFormMut_eq, genFormMut_const ell k Lu hell a Lam hN ha c]
  have hη : (PK ell k Lu hell a Lam).eta * (ell : ℝ) ^ k = 1 := by
    show ((ell : ℝ) ^ k)⁻¹ * (ell : ℝ) ^ k = 1
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    field_simp
  rw [hη]; ring

theorem exists_ne_zero_suTwo : ∃ X : SuTwo, X ≠ 0 := by
  refine ⟨⟨toM2 ![1, 0, 0], toM2_mem _⟩, fun h => ?_⟩
  have h0 : toM2 ![1, 0, 0] = 0 := congrArg Subtype.val h
  have := congrArg fromM2 h0
  rw [fromM2_toM2, map_zero] at this
  have := congrFun this 0
  simp at this

/-- **MUST-FIRE** at `k = 1`, `ell = 2`: the three natural mis-powers of `η` are refuted on the constant
mode by the proved evaluation `(η' ell^k − 1) a ‖B_c‖² ≠ 0`; the true power gives `0`. -/
theorem etaMutants_break (Lu : PeriodicLatticeExtent) (hN : ∀ μ, 1 ≤ Lu μ) (a : ℝ) (ha : 0 < a)
    (X : SuTwo) (hX : X ≠ 0) :
    let P := PK 2 1 Lu (by norm_num) a Set.univ
    let B := Bconst Lu (fun _ => X)
    genFormMut P P.eta 1 B = 0 ∧ genFormMut P (P.eta ^ 2) 1 B ≠ 0 ∧ genFormMut P 1 1 B ≠ 0 ∧
      genFormMut P (P.eta⁻¹) 1 B ≠ 0 := by
  intro P B
  have hB : 0 < ‖B‖ ^ 2 := by
    have : B ≠ 0 := by
      intro h0
      have h1 := congrFun (congrArg WithLp.ofLp h0) ((fun _ => ⟨0, Nat.succ_pos _⟩ : PeriodicLatticeSite Lu), 0)
      exact hX h1
    positivity
  have hη : P.eta = ((2 : ℝ) ^ 1)⁻¹ := rfl
  have e := fun η' => genFormMut_const 2 1 Lu (by norm_num) a Set.univ hN ha (fun _ => X) η'
  have hab : 0 < a * ‖B‖ ^ 2 := by positivity
  have v0 : genFormMut P P.eta 1 B = 0 := by rw [e, hη]; norm_num
  have v1 : genFormMut P (P.eta ^ 2) 1 B = (-(1 / 2)) * (a * ‖B‖ ^ 2) := by
    rw [e, hη]; norm_num; ring
  have v2 : genFormMut P 1 1 B = 1 * (a * ‖B‖ ^ 2) := by
    rw [e]
    show (1 * ((2 : ℕ) : ℝ) ^ 1 - 1) * a * ‖B‖ ^ 2 = 1 * (a * ‖B‖ ^ 2)
    push_cast; ring
  have v3 : genFormMut P (P.eta⁻¹) 1 B = 3 * (a * ‖B‖ ^ 2) := by
    rw [e, hη]; norm_num; ring
  refine ⟨v0, ?_, ?_, ?_⟩
  · rw [v1]; intro h; linarith
  · rw [v2]; intro h; linarith
  · rw [v3]; intro h; linarith

#print axioms genFormMut_const
#print axioms genForm_const_zero
#print axioms exists_ne_zero_suTwo
#print axioms etaMutants_break

end AdalyFormal.GenuineU1
