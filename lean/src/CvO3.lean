import CvO1

/-!
# CvO3 -- holonomy of the staggered layer along strided paths (lane omega)

`pathAng c t s y p` is the Cartan angle accumulated by `stagCfg c t` along the stride-`s` path `p` from `y`;
`hol_stag`: `coarsePathHolonomy s (stagCfg c t) y p = cartan (pathAng c t s y p)`.
Closed forms (for an EVEN transverse side `2 ∣ L 1 + 1`): along `replicate n 1` the angle is `[y₀ = c]·t·Σ_{j<n} σ(y₁ + s j)`
with `σ(v) = (-1)^v`; along `replicate n μ` for `μ ≠ 1` it is `0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (coarsePathHolonomy_cons coarsePathHolonomy_nil coarsePathEndpoint_cons
  coarsePathEndpoint_append coarsePathHolonomy_append)

variable {L : PeriodicLatticeExtent}

/-- `(-1)^v` as a real, via parity of the natural `v`. -/
def sgnNat (v : ℕ) : ℝ := if v % 2 = 0 then 1 else -1

theorem sgnNat_add_even (v w : ℕ) (hw : w % 2 = 0) : sgnNat (v + w) = sgnNat v := by
  unfold sgnNat; have : (v + w) % 2 = v % 2 := by omega
  rw [this]

theorem sgnNat_succ (v : ℕ) : sgnNat (v + 1) = - sgnNat v := by
  unfold sgnNat
  by_cases h : v % 2 = 0
  · have : (v + 1) % 2 ≠ 0 := by omega
    simp [h, this]
  · have : (v + 1) % 2 = 0 := by omega
    simp [h, this]

theorem sgnNat_mod (N v : ℕ) (hN : 2 ∣ N) : sgnNat (v % N) = sgnNat v := by
  unfold sgnNat
  have : (v % N) % 2 = v % 2 := by
    obtain ⟨m, rfl⟩ := hN
    rw [Nat.mod_mul_right_mod]
  rw [this]

/-- the angle accumulated along a stride-`s` path. -/
noncomputable def pathAng (c : ℕ) (t : ℝ) (s : ℕ) : PeriodicLatticeSite L → List (Fin 3) → ℝ
  | _, [] => 0
  | y, μ :: rest => (if (y 0).val = c ∧ μ = 1 then stagSign y * t else 0) + pathAng c t s (coarseShift y s μ) rest

theorem hol_stag (c : ℕ) (t : ℝ) (s : ℕ) (p : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, coarsePathHolonomy s (stagCfg c t) y p = cartan (pathAng c t s y p) := by
  induction p with
  | nil => intro y; rw [coarsePathHolonomy_nil]; exact cartan_zero.symm
  | cons μ rest ih =>
    intro y
    rw [coarsePathHolonomy_cons, ih]
    simp only [pathAng, stagCfg]
    by_cases h : (y 0).val = c ∧ μ = 1
    · simp only [h, and_self, if_true]; rw [cartan_mul]
    · simp only [h, if_false]; rw [one_mul, zero_add]

theorem pathAng_append (c : ℕ) (t : ℝ) (s : ℕ) (p q : List (Fin 3)) :
    ∀ y : PeriodicLatticeSite L, pathAng c t s y (p ++ q) = pathAng c t s y p + pathAng c t s (coarsePathEndpoint s y p) q := by
  induction p with
  | nil => intro y; simp [pathAng, coarsePathEndpoint]
  | cons μ rest ih =>
    intro y
    simp only [List.cons_append, pathAng, coarsePathEndpoint_cons, ih]
    ring

/-- steps in a direction `μ ≠ 1` contribute nothing. -/
theorem pathAng_rep_ne (c : ℕ) (t : ℝ) (s : ℕ) (μ : Fin 3) (hμ : μ ≠ 1) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, pathAng c t s y (List.replicate n μ) = 0 := by
  induction n with
  | zero => intro y; rfl
  | succ n ih => intro y; simp [List.replicate_succ, pathAng, hμ, ih]

/-- the stagger sign after shifting in direction `1` by `s`, for an even transverse side. -/
theorem stagSign_coarseShift_one (hN : 2 ∣ L 1 + 1) (y : PeriodicLatticeSite L) (s : ℕ) :
    stagSign (coarseShift y s 1) = sgnNat ((y 1).val + s) := by
  unfold stagSign
  rw [coarseShift_val_eq]
  have := sgnNat_mod (L 1 + 1) ((y 1).val + s) hN
  unfold sgnNat at this ⊢
  rw [← this]

theorem stagSign_eq_sgnNat (y : PeriodicLatticeSite L) : stagSign y = sgnNat (y 1).val := rfl

theorem sgnNat_mod_add (N a b : ℕ) (hN : 2 ∣ N) : sgnNat (a % N + b) = sgnNat (a + b) := by
  unfold sgnNat
  have h1 : (a % N) % 2 = a % 2 := by
    obtain ⟨m, rfl⟩ := hN
    rw [Nat.mod_mul_right_mod]
  have : (a % N + b) % 2 = (a + b) % 2 := by omega
  rw [this]

/-- along `n` steps in direction `1` from `y`: `[y₀ = c]·t·Σ_{j<n} (-1)^{y₁ + s j}`. -/
theorem pathAng_rep_one (hN : 2 ∣ L 1 + 1) (c : ℕ) (t : ℝ) (s : ℕ) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, pathAng c t s y (List.replicate n 1) =
      if (y 0).val = c then t * ∑ j ∈ Finset.range n, sgnNat ((y 1).val + s * j) else 0 := by
  induction n with
  | zero => intro y; simp [pathAng]
  | succ n ih =>
    intro y
    have h0 : (coarseShift y s 1) 0 = y 0 := coarseShift_apply_ne y s 1 0 (by decide)
    rw [List.replicate_succ, pathAng, ih, h0]
    have hshift : ∀ j, sgnNat ((coarseShift y s 1 1).val + s * j) = sgnNat ((y 1).val + s * (j + 1)) := by
      intro j
      rw [coarseShift_val_eq, sgnNat_mod_add _ _ _ hN]
      congr 1; ring
    by_cases hy : (y 0).val = c
    · simp only [hy, and_self, if_true, hshift]
      rw [Finset.sum_range_succ' (fun j => sgnNat ((y 1).val + s * j)), stagSign_eq_sgnNat]
      simp only [mul_zero, add_zero]
      ring
    · simp [hy]

end AdalyFormal.CoverOmega
