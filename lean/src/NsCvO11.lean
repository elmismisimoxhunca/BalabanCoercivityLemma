import NsCvO10
import NsCvO9

/-!
# CvO11 -- the class `𝒞(D,u)`: direction-0 links `cartan (D(z₀) u(z₁,z₂))`, directions 1,2 trivial; loops of such a configuration (lane omega)

`bg1_stag_all` (CvO10) places the first blocked level of the staggered layer in this class at EVERY base (also truncated blocks).  Here: the
holonomy calculus for the class (no coarseness assumption), the exact loop angles, and the bound
`|angle| ≤ |t|` at stride `ell` when `D(v) = [v = c] - [(v+ell) mod N₀ = c]` and `|u| ≤ |t|/2` (the profile telescopes).
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

/-- the class `𝒞(D,u)` -/
def IsUTemp (D : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (V : PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ z : PeriodicLatticeSite L, V (z, 0) = cartan (D (z 0).val * u (z 1).val (z 2).val) ∧ V (z, 1) = 1 ∧ V (z, 2) = 1

/-- angle along a stride-`s` path in the class. -/
noncomputable def uAng (s : ℕ) (D : ℕ → ℝ) (u : ℕ → ℕ → ℝ) : PeriodicLatticeSite L → List (Fin 3) → ℝ
  | _, [] => 0
  | z, μ :: rest => (if μ = 0 then D (z 0).val * u (z 1).val (z 2).val else 0) + uAng s D u (coarseShift z s μ) rest

theorem hol_uTemp {s : ℕ} {D : ℕ → ℝ} {u : ℕ → ℕ → ℝ} {V : PeriodicLinkConfiguration SU2 L} (hV : IsUTemp D u V)
    (p : List (Fin 3)) : ∀ z : PeriodicLatticeSite L, coarsePathHolonomy s V z p = cartan (uAng s D u z p) := by
  induction p with
  | nil => intro y; rw [coarsePathHolonomy_nil]; exact cartan_zero.symm
  | cons μ rest ih =>
    intro y
    rw [coarsePathHolonomy_cons, ih]
    obtain ⟨h0, h1, h2⟩ := hV y
    simp only [uAng]
    fin_cases μ
    · simp only [Fin.zero_eta, h0, if_true, cartan_mul]
    · simp only [Fin.mk_one, h1, one_mul]; simp
    · simp only [Fin.reduceFinMk, h2, one_mul]; simp

theorem uAng_append (s : ℕ) (D : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (p q : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, uAng s D u y (p ++ q) = uAng s D u y p + uAng s D u (coarsePathEndpoint s y p) q := by
  induction p with
  | nil => intro y; simp [uAng, coarsePathEndpoint]
  | cons μ rest ih =>
    intro y
    simp only [List.cons_append, uAng, coarsePathEndpoint_cons, ih]
    ring

theorem uAng_rep_ne (s : ℕ) (D : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, uAng s D u y (List.replicate n μ) = 0 := by
  induction n with
  | zero => intro y; rfl
  | succ n ih => intro y; simp [List.replicate_succ, uAng, hμ, ih]

/-- `n` steps in direction `0`: the lateral coordinates are fixed. -/
theorem uAng_rep_zero (s : ℕ) (D : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, uAng s D u y (List.replicate n 0) =
      ∑ j ∈ Finset.range n, D (((y 0).val + s * j) % (L 0 + 1)) * u (y 1).val (y 2).val := by
  induction n with
  | zero => intro y; simp [uAng]
  | succ n ih =>
    intro y
    rw [List.replicate_succ, uAng, ih, Finset.sum_range_succ' (fun j => D (((y 0).val + s * j) % (L 0 + 1)) * u (y 1).val (y 2).val)]
    simp only [if_true, mul_zero, add_zero, Nat.mod_eq_of_lt (y 0).isLt]
    have h : ∀ j, D ((((coarseShift y s 0) 0).val + s * j) % (L 0 + 1)) * u ((coarseShift y s 0) 1).val ((coarseShift y s 0) 2).val
        = D (((y 0).val + s * (j + 1)) % (L 0 + 1)) * u (y 1).val (y 2).val := by
      intro j
      rw [coarseShift_val_eq, Nat.mod_add_mod, coarseShift_apply_ne y s 0 1 (by decide), coarseShift_apply_ne y s 0 2 (by decide)]
      congr 3; ring
    simp only [h]
    ring

/-- the `μ`-coordinate after `n` steps in direction `μ`. -/
theorem endpoint_rep_self (s : ℕ) (μ : Fin 3) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, ((coarsePathEndpoint s y (List.replicate n μ)) μ).val = ((y μ).val + s * n) % (L μ + 1) := by
  induction n with
  | zero => intro y; simp [coarsePathEndpoint, Nat.mod_eq_of_lt (y μ).isLt]
  | succ n ih =>
    intro y
    rw [List.replicate_succ, coarsePathEndpoint_cons, ih, coarseShift_val_eq, Nat.mod_add_mod]
    congr 1; ring

theorem uAng_gamma (s : ℕ) (D : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (w y x : PeriodicLatticeSite L) :
    uAng s D u w (coarseGammaPath s y x) =
      ∑ j ∈ Finset.range (((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s),
        D (((w 0).val + s * j) % (L 0 + 1)) *
          u (((w 1).val + s * (((x 1 - (Function.update y 2 (x 2)) 1).val) / s)) % (L 1 + 1))
            (((w 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1)) := by
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  rw [uAng_append, uAng_rep_ne s D u 2 (by decide), uAng_append, uAng_rep_ne s D u 1 (by decide)]
  simp only [zero_add]
  rw [uAng_rep_zero]
  have h0 : ∀ n1 n2 : ℕ, (coarsePathEndpoint s (coarsePathEndpoint s w (List.replicate n2 2)) (List.replicate n1 1)) 0 = w 0 := by
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
  simp only [h0, h1, h2]

#print axioms hol_uTemp
#print axioms uAng_rep_zero
#print axioms endpoint_rep_self
#print axioms uAng_gamma

end AdalyFormal.CoverOmega
