import CB2
/-!
# AB1 -- translation geometry of strided blocks (for the abelian identity CMP98 (48))

* `shift_self`, `shift_ne`, `shift_sub`: `coarseShift · n μ` adds `n` to coordinate `μ` (mod the
  extent) and leaves the others; coordinate DIFFERENCES are translation invariant.
* `gamma_shift`: the staircase `coarseGammaPath s` is translation invariant.
* `mem_block_iff`: for a base point that FITS (`y ν + s·ell ≤ L ν + 1`), block membership is a
  condition on coordinate differences only.
* `block_sum_shift`: block sums are translation invariant when both base points fit.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarseStraightSegment coarseCoordSteps)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- `n` reduced into `Fin (N+1)`. -/
def finK (N n : ℕ) : Fin (N + 1) := ⟨n % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩

theorem shift_self (y : PeriodicLatticeSite L) (n : ℕ) (μ : Fin 3) :
    (coarseShift y n μ) μ = y μ + finK (L μ) n := by
  apply Fin.ext
  rw [AdalyFormal.Balaban.CoarseCurl.coarseShift_val_eq, Fin.val_add]
  show _ = ((y μ).val + n % (L μ + 1)) % (L μ + 1)
  rw [Nat.add_mod_mod]

theorem shift_ne (y : PeriodicLatticeSite L) (n : ℕ) {μ ν : Fin 3} (h : ν ≠ μ) :
    (coarseShift y n μ) ν = y ν := by
  induction n with
  | zero => simp [coarseShift]
  | succ k ih =>
      rw [AdalyFormal.Balaban.U1AnchorPoincare.coarseShift_succ]
      unfold periodicLatticeShift
      rw [Function.update_of_ne h, ih]

theorem shift_sub (x y : PeriodicLatticeSite L) (n : ℕ) (μ ν : Fin 3) :
    (coarseShift x n μ) ν - (coarseShift y n μ) ν = x ν - y ν := by
  by_cases h : ν = μ
  · subst h; rw [shift_self, shift_self, add_sub_add_right_eq_sub]
  · rw [shift_ne x n h, shift_ne y n h]

theorem gamma_shift (s n : ℕ) (μ : Fin 3) (y x : PeriodicLatticeSite L) :
    coarseGammaPath s (coarseShift y n μ) (coarseShift x n μ) = coarseGammaPath s y x := by
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  simp only [coarseGammaPath, coarseStraightSegment, coarseCoordSteps,
    Function.update_of_ne h12, Function.update_of_ne h02, Function.update_of_ne h01, shift_sub]

theorem mem_block_iff (s ell : ℕ) {y x : PeriodicLatticeSite L}
    (hfit : ∀ ν, (y ν).val + s * ell ≤ L ν + 1) :
    x ∈ stepBlockOf y s ell ↔ ∀ ν, (x ν - y ν).val < s * ell ∧ s ∣ (x ν - y ν).val := by
  rw [mem_stepBlockOf]
  refine forall_congr' (fun ν => ?_)
  have hf := hfit ν
  rcases le_or_gt (y ν) (x ν) with hle | hlt
  · rw [Fin.sub_val_of_le hle]
    have : (y ν).val ≤ (x ν).val := hle
    constructor
    · rintro ⟨_, h2, h3⟩; exact ⟨by omega, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨this, by omega, h3⟩
  · have hv := Fin.coe_sub_iff_lt.mpr hlt
    have hlt' : (x ν).val < (y ν).val := hlt
    have hxlt := (x ν).isLt
    constructor
    · rintro ⟨h1, _, _⟩; omega
    · rintro ⟨h2, _⟩; rw [hv] at h2; omega

/-- The translation, as an equivalence of sites. -/
def shiftEquiv (n : ℕ) (μ : Fin 3) : PeriodicLatticeSite L ≃ PeriodicLatticeSite L where
  toFun y := coarseShift y n μ
  invFun y := Function.update y μ (y μ - finK (L μ) n)
  left_inv y := by
    funext ν
    show Function.update (coarseShift y n μ) μ ((coarseShift y n μ) μ - finK (L μ) n) ν = y ν
    by_cases h : ν = μ
    · subst h; rw [Function.update_self, shift_self, add_sub_cancel_right]
    · rw [Function.update_of_ne h, shift_ne y n h]
  right_inv y := by
    funext ν
    show (coarseShift (Function.update y μ (y μ - finK (L μ) n)) n μ) ν = y ν
    by_cases h : ν = μ
    · subst h; rw [shift_self, Function.update_self, sub_add_cancel]
    · rw [shift_ne _ n h, Function.update_of_ne h]

theorem block_sum_shift {β : Type*} [AddCommMonoid β] (s ell n : ℕ) (μ : Fin 3)
    {y : PeriodicLatticeSite L}
    (hfit : ∀ ν, (y ν).val + s * ell ≤ L ν + 1)
    (hfit' : ∀ ν, ((coarseShift y n μ) ν).val + s * ell ≤ L ν + 1)
    (F : PeriodicLatticeSite L → β) :
    ∑ x ∈ stepBlockOf y s ell, F (coarseShift x n μ)
      = ∑ x ∈ stepBlockOf (coarseShift y n μ) s ell, F x := by
  refine Finset.sum_equiv (shiftEquiv n μ) (fun x => ?_) (fun x _ => rfl)
  rw [mem_block_iff s ell hfit, mem_block_iff s ell hfit']
  have hsub : ∀ ν, (shiftEquiv n μ x) ν - (coarseShift y n μ) ν = x ν - y ν :=
    fun ν => shift_sub x y n μ ν
  simp only [hsub]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.gamma_shift
#print axioms AdalyFormal.CurvBlock.mem_block_iff
#print axioms AdalyFormal.CurvBlock.block_sum_shift
