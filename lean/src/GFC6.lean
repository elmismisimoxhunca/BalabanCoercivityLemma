import GFC4
import GFC5

/-!
# GFC6 -- the concrete twisted-cell model: lifts, twisted shifts `S_μ(z)`, and the `SymData` instance.

Cell vectors `v : CV n = EuclideanSpace ℂ (Cell n)`; twist parameters `z : Fin 3 → Circle`.
`lift z v` is the quasi-periodic extension to `ℤ³` (`lift z v (x + n k) = phase z k * lift z v x`),
`S_μ(z) v = (t ↦ lift z v (t + e_μ))`.   Standard axioms only.
-/
set_option autoImplicit false
open scoped ComplexInnerProductSpace BigOperators

namespace AdalyFormal.FlatCoercivity

abbrev CV (n : ℕ) := EuclideanSpace ℂ (Cell n)

/-- the quasi-periodicity phase `∏ z_μ^{k_μ}` -/
noncomputable def phase (z : Fin 3 → ℂ) (k : Z3) : ℂ := ∏ μ, (z μ) ^ (k μ)

section phase
variable {z : Fin 3 → ℂ}

theorem phase_add (hz : ∀ μ, z μ ≠ 0) (k k' : Z3) : phase z (k + k') = phase z k * phase z k' := by
  simp only [phase, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun μ _ => zpow_add₀ (hz μ) _ _)

theorem phase_zero : phase z 0 = 1 := by simp [phase]

theorem phase_ev (μ : Fin 3) : phase z (ev μ) = z μ := by
  unfold phase ev
  rw [Finset.prod_eq_single μ]
  · simp
  · intro ν _ hν; simp [Pi.single_apply, hν]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem norm_phase (hz : ∀ μ, ‖z μ‖ = 1) (k : Z3) : ‖phase z k‖ = 1 := by
  unfold phase
  rw [norm_prod]
  refine Finset.prod_eq_one (fun μ _ => ?_)
  rw [norm_zpow, hz μ, one_zpow]

theorem phase_one (hz : ∀ μ, z μ = 1) (k : Z3) : phase z k = 1 := by
  unfold phase
  exact Finset.prod_eq_one (fun μ _ => by rw [hz μ, one_zpow])

end phase

variable {n : ℕ}

/-- quasi-periodic lift of a cell vector -/
noncomputable def lift (hn : 0 < n) (z : Fin 3 → ℂ) (v : CV n) (x : Z3) : ℂ :=
  phase z (fun μ => x μ / (n : ℤ)) * v (modc n hn x)

theorem lift_qp (hn : 0 < n) {z : Fin 3 → ℂ} (hz : ∀ μ, z μ ≠ 0) (v : CV n) (x k : Z3) :
    lift hn z v (x + (n : ℤ) • k) = phase z k * lift hn z v x := by
  unfold lift
  have h1 : (fun μ => (x + (n : ℤ) • k) μ / (n : ℤ)) = (fun μ => x μ / (n : ℤ)) + k := by
    funext μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.add_mul_ediv_left _ _ (by exact_mod_cast hn.ne')]
  rw [h1, modc_add, phase_add hz]
  ring

theorem lift_cc (hn : 0 < n) (z : Fin 3 → ℂ) (v : CV n) (t : Cell n) : lift hn z v (cc t) = v t := by
  unfold lift
  have : (fun μ => cc t μ / (n : ℤ)) = 0 := by
    funext μ
    simp only [cc, Pi.zero_apply]
    exact Int.ediv_eq_zero_of_lt (by simp) (by exact_mod_cast (t μ).isLt)
  rw [this, phase_zero, modc_cc, one_mul]

theorem lift_add (hn : 0 < n) (z : Fin 3 → ℂ) (v w : CV n) (x : Z3) :
    lift hn z (v + w) x = lift hn z v x + lift hn z w x := by
  unfold lift; simp [mul_add]

theorem lift_smul (hn : 0 < n) (z : Fin 3 → ℂ) (c : ℂ) (v : CV n) (x : Z3) :
    lift hn z (c • v) x = c * lift hn z v x := by
  unfold lift; simp [mul_left_comm]

/-- the twisted shift as a linear map -/
noncomputable def Sl (hn : 0 < n) (z : Fin 3 → ℂ) (μ : Fin 3) : CV n →ₗ[ℂ] CV n where
  toFun v := WithLp.toLp 2 (fun t => lift hn z v (cc t + ev μ))
  map_add' v w := by ext t; simp [lift_add]
  map_smul' c v := by ext t; simp [lift_smul]

theorem Sl_apply (hn : 0 < n) (z : Fin 3 → ℂ) (μ : Fin 3) (v : CV n) (t : Cell n) :
    Sl hn z μ v t = lift hn z v (cc t + ev μ) := rfl

theorem lift_Sl (hn : 0 < n) {z : Fin 3 → ℂ} (hz : ∀ μ, z μ ≠ 0) (μ : Fin 3) (v : CV n) (x : Z3) :
    lift hn z (Sl hn z μ v) x = lift hn z v (x + ev μ) := by
  have hx := eq_cc_modc_add hn x
  have h2 : x + ev μ = (cc (modc n hn x) + ev μ) + (n : ℤ) • (fun ν => x ν / (n : ℤ)) := by
    conv_lhs => rw [hx]
    abel
  calc lift hn z (Sl hn z μ v) x
      = phase z (fun ν => x ν / (n : ℤ)) * Sl hn z μ v (modc n hn x) := rfl
    _ = phase z (fun ν => x ν / (n : ℤ)) * lift hn z v (cc (modc n hn x) + ev μ) := by
        rw [Sl_apply]
    _ = lift hn z v (x + ev μ) := by rw [h2, lift_qp hn hz]

theorem Sl_iter (hn : 0 < n) {z : Fin 3 → ℂ} (hz : ∀ μ, z μ ≠ 0) (μ : Fin 3) (i : ℕ) (v : CV n) (t : Cell n) :
    ((Sl hn z μ)^[i] v) t = lift hn z v (cc t + (i : ℤ) • ev μ) := by
  induction i generalizing v with
  | zero => simp [lift_cc]
  | succ i ih =>
      rw [Function.iterate_succ_apply, ih, lift_Sl hn hz]
      congr 1
      rw [Nat.cast_succ, add_smul, one_smul]
      abel

theorem norm_Sl (hn : 0 < n) {z : Fin 3 → ℂ} (hz : ∀ μ, ‖z μ‖ = 1) (μ : Fin 3) (v : CV n) :
    ‖Sl hn z μ v‖ = ‖v‖ := by
  have hz0 : ∀ μ, z μ ≠ 0 := fun μ h => by have := hz μ; rw [h] at this; simp at this
  have h1 : ‖Sl hn z μ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have : ∀ t, ‖Sl hn z μ v t‖ ^ 2 = ‖v (cellShift hn (ev μ) t)‖ ^ 2 := by
      intro t
      rw [Sl_apply]
      unfold lift
      rw [norm_mul, norm_phase hz, one_mul]
      rfl
    simp only [this]
    exact Equiv.sum_comp (cellShift hn (ev μ)) (fun t => ‖v t‖ ^ 2)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1


/-- the twisted shift as a unitary -/
noncomputable def Su (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) : CV n ≃ₗᵢ[ℂ] CV n :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := Sl hn (fun μ => (z μ : ℂ)) μ
      norm_map' := norm_Sl hn (fun μ => Circle.norm_coe (z μ)) μ } rfl

theorem Su_apply (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) (v : CV n) :
    Su hn z μ v = Sl hn (fun μ => (z μ : ℂ)) μ v := rfl

theorem z_ne (z : Fin 3 → Circle) : ∀ μ, ((z μ : Circle) : ℂ) ≠ 0 := fun μ => by
  have := Circle.norm_coe (z μ); intro h; rw [h] at this; simp at this

theorem Su_comm (hn : 0 < n) (z : Fin 3 → Circle) (μ ν : Fin 3) (v : CV n) :
    Su hn z μ (Su hn z ν v) = Su hn z ν (Su hn z μ v) := by
  ext t
  simp only [Su_apply, Sl_apply]
  rw [lift_Sl hn (z_ne z), lift_Sl hn (z_ne z)]
  congr 1
  abel

theorem Su_pow (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) (v : CV n) :
    (Su hn z μ)^[n] v = ((z μ : Circle) : ℂ) • v := by
  ext t
  have h1 : ((Su hn z μ)^[n] v) t = ((Sl hn (fun μ => (z μ : ℂ)) μ)^[n] v) t := rfl
  rw [h1, Sl_iter hn (z_ne z), lift_qp hn (z_ne z), lift_cc, phase_ev]
  rfl

/-- the all-ones cell vector -/
noncomputable def epsV (n : ℕ) : CV n := WithLp.toLp 2 (fun _ => (1 : ℂ))

theorem epsV_ne (hn : 0 < n) : epsV n ≠ 0 := by
  intro h
  have := congrFun (congrArg WithLp.ofLp h) (modc n hn 0)
  simp [epsV] at this

theorem epsV_fixed (hn : 0 < n) (z : Fin 3 → Circle) (hz : ∀ μ, ((z μ : Circle) : ℂ) = 1) (μ : Fin 3) :
    Su hn z μ (epsV n) = epsV n := by
  ext t
  rw [Su_apply, Sl_apply]
  unfold lift
  rw [phase_one hz]
  simp [epsV]

theorem const_of_step (f : Z3 → ℂ) (h : ∀ x μ, f (x + ev μ) = f x) : ∀ x, f x = f 0 := by
  have h1 : ∀ (μ : Fin 3) (a : ℤ) (x : Z3), f (x + a • ev μ) = f x := by
    intro μ a x
    induction a using Int.induction_on with
    | zero => simp
    | succ a ih =>
        have : x + ((a : ℤ) + 1) • ev μ = (x + (a : ℤ) • ev μ) + ev μ := by
          rw [add_smul, one_smul]; abel
        rw [this, h, ih]
    | pred a ih =>
        have : x + (-(a : ℤ) - 1) • ev μ + ev μ = x + (-(a : ℤ)) • ev μ := by
          rw [sub_smul, one_smul]; abel
        rw [← ih, ← this, h]
  intro x
  have hx : x = (0 : Z3) + x 0 • ev 0 + x 1 • ev 1 + x 2 • ev 2 := by
    funext μ
    fin_cases μ <;> simp [ev, Pi.single_apply]
  rw [hx, h1, h1, h1]

theorem fixed_const (hn : 0 < n) (z : Fin 3 → Circle) (hz : ∀ μ, ((z μ : Circle) : ℂ) = 1)
    (w : CV n) (hw : ∀ μ, Su hn z μ w = w) : ∀ t, w t = w (modc n hn 0) := by
  set f : Z3 → ℂ := lift hn (fun μ => (z μ : ℂ)) w with hf
  have hfm : ∀ x, f x = w (modc n hn x) := by
    intro x; rw [hf]; unfold lift; rw [phase_one hz, one_mul]
  have hstep : ∀ x μ, f (x + ev μ) = f x := by
    intro x μ
    rw [hfm, hfm]
    have hx := eq_cc_modc_add hn x
    have : x + ev μ = (cc (modc n hn x) + ev μ) + (n : ℤ) • (fun ν => x ν / (n : ℤ)) := by
      conv_lhs => rw [hx]
      abel
    rw [this, modc_add]
    have h2 := congrFun (congrArg WithLp.ofLp (hw μ)) (modc n hn x)
    rw [Su_apply, Sl_apply] at h2
    have h3 : lift hn (fun μ => (z μ : ℂ)) w (cc (modc n hn x) + ev μ) = w (modc n hn (cc (modc n hn x) + ev μ)) := by
      unfold lift; rw [phase_one hz, one_mul]
    rw [← h3]; exact h2
  intro t
  have := const_of_step f hstep (cc t)
  rw [hfm, hfm] at this
  rw [modc_cc] at this
  exact this

theorem fixed_span (hn : 0 < n) (z : Fin 3 → Circle) (hz : ∀ μ, ((z μ : Circle) : ℂ) = 1)
    (w : CV n) (hw : ∀ μ, Su hn z μ w = w) : ∃ c : ℂ, w = c • epsV n := by
  refine ⟨w (modc n hn 0), ?_⟩
  ext t
  rw [fixed_const hn z hz w hw t]
  simp [epsV]

/-- the symbol data of the twisted cell -/
noncomputable def cellSym (hn : 0 < n) (z : Fin 3 → Circle) : SymData (CV n) where
  n := n
  hn := hn
  S := Su hn z
  comm := fun μ ν x => Su_comm hn z μ ν x
  ph := fun μ => ((z μ : Circle) : ℂ)
  Spow := fun μ x => Su_pow hn z μ x
  eps := epsV n
  eps_ne := epsV_ne hn
  eps_fixed := fun hz μ => epsV_fixed hn z hz μ
  fixed_span := fun hz w hw => fixed_span hn z hz w hw

#print axioms cellSym
#print axioms fixed_span

end AdalyFormal.FlatCoercivity
