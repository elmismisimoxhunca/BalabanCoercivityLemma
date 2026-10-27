import ZT5A
import ZGU1N

/-!
# ZT5B -- (8) the PX1 instance, re-run at `k ≥ 1` against the r5 statement.

PX1 (r3 Opus prosecution): `ell = 2`, `M = 1`, full tower, flat `U`, unit torus `L10`, `Λ = LamX = {not all coordinates odd}` (so `Λ' = ∅`,
`C = id`, the constant field is an admissible `B̃` with `(3.156) = 0`).  r3 refuted `P428Genuine` at `k = 0`; `k = 0` is now outside the range, so here
the same instance is run at EVERY `k ≥ 1` (full tower of height `k`, `Ω₀ = Ω₁ = … = Ω_k = torus`, collar law satisfied):

* `px1_refutes_NB`: the r5 inner claim WITHOUT the printed decomposition `Λ = B(Λ')` (hypothesis `LambdaOK` only) is FALSE at `(2,1,k≥1)`, for every `γ₀ > 0, α₀ > 0, a > 0, R`;
* `px1_not_lambdaOK2`: the PX1 `Λ` violates the r5 hypothesis `LambdaOK2`; `px1_not_side5`: `(ell, M) = (2, 1)` violates both side conditions;
  `px1_not_P428Genuine8`;
* the mechanism for any `ell ≥ 2`: `const_not_tilde_of_blockSum`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath mem_axisSegment)
open AdalyFormal.Balaban.ReparamCDisjoint (coarse_coord_add_ell_le)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- the PX1 set `Λ = {not all coordinates odd}` on the unit torus `L10` -/
def LamX : Set (PeriodicLatticeSite L10) := {x | ¬ ∀ μ : Fin 3, (x μ).val % 2 = 1}

theorem lamPrime_empty : LamPrime 2 LamX = ∅ := by
  ext y
  simp only [LamPrime, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hy, hall⟩
  rw [mem_CoarseLattice] at hy
  let x : PeriodicLatticeSite L10 := fun μ => ⟨(y μ).val + 1, by
    have h1 := (y μ).isLt
    have h2 := hy μ
    have h3 : L10 μ = 9 := rfl
    omega⟩
  have hx : x ∈ blockOf y 2 := by
    rw [mem_blockOf]; intro μ; simp [x]
  have hX := hall x hx
  apply hX
  intro μ
  have h2 := hy μ
  show ((y μ).val + 1) % 2 = 1
  omega

theorem not_dropped (b : Bond L10) : ¬ IsDroppedIn LamX 2 b := by
  rintro ⟨c, hc, _⟩
  rcases hc with h | h <;> (rw [lamPrime_empty] at h; exact h)

theorem tilde_all (Bt : Bond L10 → SuTwo) : OnLambdaTildeIn LamX 2 Bt := by
  refine ⟨fun y hy => ?_, fun b hb => absurd hb (not_dropped b)⟩
  rw [lamPrime_empty] at hy
  exact absurd hy (Set.notMem_empty y)

theorem touches (b : Bond L10) : b.1 ∈ LamX ∨ periodicLatticeShift b.1 b.2 ∈ LamX := by
  by_cases h : b.1 ∈ LamX
  · exact Or.inl h
  · right
    simp only [LamX, Set.mem_setOf_eq, not_not] at h ⊢
    intro hall
    have h1 := h b.2
    have h2 := hall b.2
    have hs : (periodicLatticeShift b.1 b.2) b.2 = b.1 b.2 + 1 := by
      simp [periodicLatticeShift]
    rw [hs] at h2
    have key : ∀ z : Fin 10, z.val % 2 = 1 → (z + 1).val % 2 = 1 → False := by decide
    exact key (b.1 b.2) h1 h2

theorem touchT (Bt : Bond L10 → SuTwo) : OnLambdaT LamX Bt := by
  intro b hb; exact absurd (touches b) hb

/-- the PX1 `Λ` satisfies the OLD hypothesis `LambdaOK` on the full tower of every height `k` -/
theorem lambdaOK_X (k R : ℕ) :
    LambdaOK (Lu := L10) (Lf := scaleUp 2 k L10) 2 1 R k (fullTower 2 k L10) LamX := by
  have hf : ∀ μ, scaleUp 2 k L10 μ + 1 = (L10 μ + 1) * 2 ^ k := by
    intro μ
    have : 0 < (L10 μ + 1) * 2 ^ k := Nat.mul_pos (Nat.succ_pos _) (pow_pos (by norm_num) k)
    simp only [scaleUp]
    omega
  have h := Sk_lambdaOK (Lu := L10) (Lf := scaleUp 2 k L10) k R hf
  obtain ⟨_, emb, he1, he2, he3⟩ := h
  refine ⟨?_, emb, he1, fun y _ => he2 y (Set.mem_univ y), fun y _ y' hy' => he3 y (Set.mem_univ y) y' hy'⟩
  intro x hx y hy
  have : y = x := by
    funext μ; apply Fin.ext; have := hy μ; simpa using this
  rw [this]; exact hx

theorem genC_id (k : ℕ) (h2 : 0 < 2) (a : ℝ) (Bt : Bond L10 → SuTwo) :
    GenP.genC (gparams 2 k L10 h2 (fullTower 2 k L10) flatCfg a LamX) Bt = Bt := by
  funext b
  exact Cop_id LamX _ Bt b (not_dropped b)

theorem bondEnergy_const_pos (X : SuTwo) (hX : X ≠ 0) : 0 < bondEnergy (fun _ : Bond L10 => X) := by
  unfold bondEnergy
  have hp : 0 < ‖X‖ ^ 2 := by positivity
  have : ∑ _b : Bond L10, ‖X‖ ^ 2 = (Fintype.card (Bond L10) : ℝ) * ‖X‖ ^ 2 := by simp
  rw [this]
  have hc : (0 : ℝ) < Fintype.card (Bond L10) := by exact_mod_cast Fintype.card_pos
  positivity

/-- the constant mode is a ZERO of the genuine (3.156) form at the PX1 point, every `k` -/
theorem genForm_const_zero_X (k : ℕ) (h2 : 0 < 2) (a : ℝ) (ha : 0 < a) (X : SuTwo) :
    GenP.genForm (gparams 2 k L10 h2 (fullTower 2 k L10) flatCfg a LamX)
      (WithLp.toLp 2 (GenP.genC (gparams 2 k L10 h2 (fullTower 2 k L10) flatCfg a LamX)
        (fun _ => X))) = 0 := by
  rw [genC_id]
  have hN : ∀ μ, 1 ≤ L10 μ := by intro μ; simp [L10]
  exact AdalyFormal.GenuineU1.genForm_const_zero 2 k L10 h2 a LamX hN ha (fun _ => X)

/-- the r5 inner claim WITHOUT `Λ = B(Λ')` (hypothesis `LambdaOK` only): the r3 shape -/
def CoercG8AtNB (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

/-- **PX1 at `k ≥ 1` REFUTES the claim without the printed decomposition `Λ = B(Λ')`**, at every `γ₀ > 0`, `α₀ > 0`, `R`, `a > 0`. -/
theorem px1_refutes_NB (k : ℕ) (hk : 1 ≤ k) (R : ℕ) (a : ℝ) (ha : 0 < a) {α₀ γ₀ : ℝ} (hα : 0 < α₀)
    (hγ : 0 < γ₀) (h2 : 0 < 2) : ¬ CoercG8AtNB 2 1 R k h2 a L10 12 α₀ γ₀ := by
  intro h
  obtain ⟨hT, hA, hC, _, hP, _⟩ := genuine_point_hyps k hk R hα
  have hco := h hT (fullTower 2 k L10) hA LamX (lambdaOK_X k R) flatCfg ⟨hC, hP⟩
  obtain ⟨X, hX⟩ : ∃ X : SuTwo, X ≠ 0 := exists_ne 0
  have h1 := hco (fun _ => X) (tilde_all _) (touchT _)
  rw [genForm_const_zero_X k h2 a ha X] at h1
  have := bondEnergy_const_pos X hX
  nlinarith

/-- the PX1 `Λ` violates `Λ = B(Λ')` -/
theorem px1_not_lamBlockSum : ¬ LamBlockSum 2 (LamX : Set (PeriodicLatticeSite L10)) := by
  intro h
  have hne : (LamX : Set (PeriodicLatticeSite L10)).Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    simp only [LamX, Set.mem_setOf_eq]
    intro h
    have := h 0
    simp at this
  have := h.lamPrime_nonempty hne
  rw [lamPrime_empty] at this
  exact Set.not_nonempty_empty this

/-- the PX1 instance violates the r5 hypothesis `LambdaOK2`, every `k, R` -/
theorem px1_not_lambdaOK2 (k R : ℕ) :
    ¬ LambdaOK2 (Lu := L10) (Lf := scaleUp 2 k L10) 2 1 R k (fullTower 2 k L10) LamX :=
  fun h => px1_not_lamBlockSum h.2

/-- the PX1 parameters `(ell, M) = (2, 1)` violate both side conditions of r5 -/
theorem px1_not_side5 (a : ℝ) : ¬ SideDvd6 2 1 a ∧ ¬ SidePow6 2 1 a := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.2.2.1; omega
  · obtain ⟨m, hm, h1⟩ := h.2.1
    have h2 : 2 ^ m ≥ 2 := by
      calc 2 ^ m ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm
        _ = 2 := by norm_num
    omega

theorem px1_not_P428Genuine8 (R : ℕ) (a : ℝ) (h2 : 0 < 2) : ¬ P428Genuine8 2 1 R h2 a :=
  fun h => (px1_not_side5 a).2 h.1

/-- the constant field leaves `Λ̃` as soon as `Λ'` has a member (mechanism, any `ell ≥ 2`) -/
theorem const_not_tilde {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) {Lam : Set (PeriodicLatticeSite Lu)}
    {y : PeriodicLatticeSite Lu} (hy : y ∈ LamPrime ell Lam) (X : SuTwo) (hX : X ≠ 0) :
    ¬ OnLambdaTildeIn Lam ell (fun _ => X) := by
  intro h
  have hcoarse := hy.1
  have hfit := coarse_coord_add_ell_le hdvd 2 (y 2).val (mem_CoarseLattice.mp hcoarse 2) (y 2).isLt
  let x : PeriodicLatticeSite Lu := Function.update y 2 ⟨(y 2).val + 1, by omega⟩
  have hx : x ∈ blockOf y ell := by
    rw [mem_blockOf]; intro μ
    by_cases hμ : μ = 2
    · subst hμ; simp only [x, Function.update_self]; omega
    · simp only [x, Function.update_of_ne hμ]; omega
  have hb : ((y, (2 : Fin 3)) : Bond Lu) ∈ staircasePath y x := by
    simp only [staircasePath, Finset.mem_union]
    left; left
    rw [mem_axisSegment]
    refine ⟨rfl, fun ν hν => rfl, ?_, ?_⟩ <;> simp only [x, Function.update_self] <;> omega
  exact hX (h.1 y hy x hx _ hb)

theorem const_not_tilde_of_blockSum {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ Lu μ + 1) {Lam : Set (PeriodicLatticeSite Lu)}
    (hB : LamBlockSum ell Lam) (hne : Lam.Nonempty) (X : SuTwo) (hX : X ≠ 0) :
    ¬ OnLambdaTildeIn Lam ell (fun _ => X) := by
  obtain ⟨y, hy⟩ := hB.lamPrime_nonempty hne
  exact const_not_tilde hell2 hdvd hy X hX

theorem lamPrime_empty_iff_lam_empty {Lu : PeriodicLatticeExtent} {ell : ℕ}
    (hell : 0 < ell) {Lam : Set (PeriodicLatticeSite Lu)} (h : LamBlockSum ell Lam) :
    LamPrime ell Lam = ∅ ↔ Lam = ∅ := by
  constructor
  · intro hp
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨y, hy, _⟩ := h x hx
    rw [hp] at hy
    exact hy
  · intro hl
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    have hyb : y ∈ blockOf y ell := by
      rw [mem_blockOf]
      intro μ
      exact ⟨le_rfl, by omega⟩
    have := hy.2 y hyb
    rw [hl] at this
    exact this

#print axioms lamPrime_empty
#print axioms lambdaOK_X
#print axioms genForm_const_zero_X
#print axioms px1_refutes_NB
#print axioms px1_not_lambdaOK2
#print axioms px1_not_side5
#print axioms px1_not_P428Genuine8
#print axioms const_not_tilde_of_blockSum
#print axioms lamPrime_empty_iff_lam_empty

end AdalyFormal.StatementLaneG
