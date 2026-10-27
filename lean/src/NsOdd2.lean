import NsOdd1

/-!
# NsOdd2 -- Cartan fields with prescribed direction-0 / direction-1 value profiles: exact path angles (lane ncwdh_strong_20261017)

`fld A0 A1` is the angle field with `θ(z, 0) = A0 z₀ z₁ z₂`, `θ(z, 1) = A1 z₀ z₁ z₂` (functions of the coordinate VALUES) and `θ(z, 2) = 0`.
`pathAngG_fld_rep0/1/2` and `pathAngG_fld_gamma` give the angle along a strided straight segment and along the staircase `Γ_{y,x}`
(dir 2, then dir 1, then dir 0) as explicit finite sums.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf coarsePathHolonomy_cons coarsePathHolonomy_nil coarsePathEndpoint_cons
  coarsePathEndpoint_append coarsePathHolonomy_append)

variable {L : PeriodicLatticeExtent}

/-- the angle field with direction-0 profile `A0`, direction-1 profile `A1` (functions of the coordinate values), direction 2 trivial. -/
noncomputable def fld (A0 A1 : ℕ → ℕ → ℕ → ℝ) : PeriodicLatticeEdge L → ℝ :=
  fun e => if e.2 = 0 then A0 (e.1 0).val (e.1 1).val (e.1 2).val
    else if e.2 = 1 then A1 (e.1 0).val (e.1 1).val (e.1 2).val else 0

theorem fld_add (A0 A1 B0 B1 : ℕ → ℕ → ℕ → ℝ) :
    (fld A0 A1 : PeriodicLatticeEdge L → ℝ) + fld B0 B1 = fld (fun a b c => A0 a b c + B0 a b c) (fun a b c => A1 a b c + B1 a b c) := by
  funext e; simp only [fld, Pi.add_apply]; split_ifs <;> ring

theorem fld_smul (r : ℝ) (A0 A1 : ℕ → ℕ → ℕ → ℝ) :
    r • (fld A0 A1 : PeriodicLatticeEdge L → ℝ) = fld (fun a b c => r * A0 a b c) (fun a b c => r * A1 a b c) := by
  funext e; simp only [fld, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `n` steps in direction `0`. -/
theorem pathAngG_fld_rep0 (s : ℕ) (A0 A1 : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (fld A0 A1) y (List.replicate n 0) =
      ∑ j ∈ Finset.range n, A0 (((y 0).val + s * j) % (L 0 + 1)) (y 1).val (y 2).val := by
  induction n with
  | zero => intro y; simp [pathAngG]
  | succ n ih =>
    intro y
    rw [List.replicate_succ, pathAngG, ih, Finset.sum_range_succ' (fun j => A0 (((y 0).val + s * j) % (L 0 + 1)) (y 1).val (y 2).val)]
    simp only [fld, if_true, mul_zero, add_zero, Nat.mod_eq_of_lt (y 0).isLt]
    have h : ∀ j, A0 ((((coarseShift y s 0) 0).val + s * j) % (L 0 + 1)) ((coarseShift y s 0) 1).val ((coarseShift y s 0) 2).val
        = A0 (((y 0).val + s * (j + 1)) % (L 0 + 1)) (y 1).val (y 2).val := by
      intro j
      rw [coarseShift_val_eq, Nat.mod_add_mod, coarseShift_apply_ne y s 0 1 (by decide), coarseShift_apply_ne y s 0 2 (by decide)]
      congr 2; ring
    simp only [h]
    ring

/-- `n` steps in direction `1`. -/
theorem pathAngG_fld_rep1 (s : ℕ) (A0 A1 : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (fld A0 A1) y (List.replicate n 1) =
      ∑ j ∈ Finset.range n, A1 (y 0).val (((y 1).val + s * j) % (L 1 + 1)) (y 2).val := by
  induction n with
  | zero => intro y; simp [pathAngG]
  | succ n ih =>
    intro y
    rw [List.replicate_succ, pathAngG, ih, Finset.sum_range_succ' (fun j => A1 (y 0).val (((y 1).val + s * j) % (L 1 + 1)) (y 2).val)]
    simp only [fld, if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_true, mul_zero, add_zero, Nat.mod_eq_of_lt (y 1).isLt]
    have h : ∀ j, A1 ((coarseShift y s 1) 0).val ((((coarseShift y s 1) 1).val + s * j) % (L 1 + 1)) ((coarseShift y s 1) 2).val
        = A1 (y 0).val (((y 1).val + s * (j + 1)) % (L 1 + 1)) (y 2).val := by
      intro j
      rw [coarseShift_val_eq, Nat.mod_add_mod, coarseShift_apply_ne y s 1 0 (by decide), coarseShift_apply_ne y s 1 2 (by decide)]
      congr 2; ring
    simp only [h]
    ring

/-- `n` steps in direction `2`. -/
theorem pathAngG_fld_rep2 (s : ℕ) (A0 A1 : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, pathAngG s (fld A0 A1) y (List.replicate n 2) = 0 := by
  induction n with
  | zero => intro y; simp [pathAngG]
  | succ n ih =>
    intro y
    simp [List.replicate_succ, pathAngG, ih, fld]

/-- the angle along the staircase `Γ_{y,x}` read from an arbitrary base `w` (stride `s`). -/
theorem pathAngG_fld_gamma (s : ℕ) (A0 A1 : ℕ → ℕ → ℕ → ℝ) (w y x : PeriodicLatticeSite L) :
    pathAngG s (fld A0 A1) w (coarseGammaPath s y x) =
      ∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s),
        A1 (w 0).val (((w 1).val + s * j) % (L 1 + 1)) (((w 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)) +
      ∑ i ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
        A0 (((w 0).val + s * i) % (L 0 + 1)) (((w 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
          (((w 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)) := by
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  rw [pathAngG_append, pathAngG_fld_rep2, pathAngG_append, pathAngG_fld_rep1]
  simp only [zero_add]
  rw [pathAngG_fld_rep0]
  have h0 : ∀ n1 n2 : ℕ, ((coarsePathEndpoint s (coarsePathEndpoint s w (List.replicate n2 2)) (List.replicate n1 1)) 0).val = (w 0).val := by
    intro n1 n2
    rw [endpoint_rep_ne s 1 0 (by decide), endpoint_rep_ne s 2 0 (by decide)]
  have h1 : ∀ n1 n2 : ℕ, ((coarsePathEndpoint s (coarsePathEndpoint s w (List.replicate n2 2)) (List.replicate n1 1)) 1).val
      = ((w 1).val + s * n1) % (L 1 + 1) := by
    intro n1 n2
    rw [endpoint_rep_self, endpoint_rep_ne s 2 1 (by decide)]
  have h2 : ∀ n1 n2 : ℕ, ((coarsePathEndpoint s (coarsePathEndpoint s w (List.replicate n2 2)) (List.replicate n1 1)) 2).val
      = ((w 2).val + s * n2) % (L 2 + 1) := by
    intro n1 n2
    rw [endpoint_rep_ne s 1 2 (by decide), endpoint_rep_self]
  have e1 : ∀ n2 : ℕ, ((coarsePathEndpoint s w (List.replicate n2 2)) 0).val = (w 0).val := by
    intro n2; rw [endpoint_rep_ne s 2 0 (by decide)]
  have e1' : ∀ n2 : ℕ, ((coarsePathEndpoint s w (List.replicate n2 2)) 1).val = (w 1).val := by
    intro n2; rw [endpoint_rep_ne s 2 1 (by decide)]
  have e2 : ∀ n2 : ℕ, ((coarsePathEndpoint s w (List.replicate n2 2)) 2).val = ((w 2).val + s * n2) % (L 2 + 1) := by
    intro n2; rw [endpoint_rep_self]
  simp only [h0, h1, h2, e1, e1', e2]

#print axioms pathAngG_fld_rep0
#print axioms pathAngG_fld_rep1
#print axioms pathAngG_fld_gamma

end AdalyFormal.CoverOmega
