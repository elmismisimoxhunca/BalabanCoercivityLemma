import Mathlib

/-!
# GFC5 -- ABSTRACT symbol positivity (operator algebra only)

`V` finite-dimensional complex Hilbert space, three commuting unitaries `S μ` with `(S μ)^n = ph μ`, a vector `ε`.
`D μ = S μ - 1`, `Ds μ = (S μ)⁻¹ - 1`.  Pointwise positivity of the Bloch symbol: see `symbol_positive`.
Standard axioms only.
-/
set_option autoImplicit false
open scoped ComplexInnerProductSpace
open Finset

namespace AdalyFormal.FlatCoercivity

section Abstract
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- data of the (twisted-cell) symbol -/
structure SymData (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  n : ℕ
  hn : 0 < n
  S : Fin 3 → V ≃ₗᵢ[ℂ] V
  comm : ∀ μ ν x, S μ (S ν x) = S ν (S μ x)
  ph : Fin 3 → ℂ
  Spow : ∀ μ x, (S μ)^[n] x = ph μ • x
  eps : V
  eps_ne : eps ≠ 0
  eps_fixed : (∀ μ, ph μ = 1) → ∀ μ, S μ eps = eps
  fixed_span : (∀ μ, ph μ = 1) → ∀ w, (∀ μ, S μ w = w) → ∃ c : ℂ, w = c • eps

namespace SymData
variable (sd : SymData V)

/-- forward difference -/
def D (μ : Fin 3) (x : V) : V := sd.S μ x - x
/-- backward difference (the adjoint of `D`) -/
def Ds (μ : Fin 3) (x : V) : V := (sd.S μ).symm x - x

theorem inner_D (μ : Fin 3) (x y : V) : ⟪sd.D μ x, y⟫ = ⟪x, sd.Ds μ y⟫ := by
  unfold D Ds
  rw [inner_sub_left, inner_sub_right]
  congr 1
  rw [← (sd.S μ).inner_map_map x ((sd.S μ).symm y)]
  simp

theorem inner_Ds (μ : Fin 3) (x y : V) : ⟪sd.Ds μ x, y⟫ = ⟪x, sd.D μ y⟫ := by
  rw [← inner_conj_symm, ← inner_conj_symm x, inner_D]

theorem D_D (μ ν : Fin 3) (x : V) : sd.D μ (sd.D ν x) = sd.D ν (sd.D μ x) := by
  unfold D
  simp only [map_sub, sd.comm μ ν x]
  abel

theorem Ds_D (μ ν : Fin 3) (x : V) : sd.Ds μ (sd.D ν x) = sd.D ν (sd.Ds μ x) := by
  unfold D Ds
  simp only [map_sub]
  have : (sd.S μ).symm (sd.S ν x) = sd.S ν ((sd.S μ).symm x) := by
    apply (sd.S μ).injective
    rw [LinearIsometryEquiv.apply_symm_apply, sd.comm μ ν, LinearIsometryEquiv.apply_symm_apply]
  rw [this]
  abel

/-- the lattice Laplacian -/
def Lap (x : V) : V := ∑ μ, sd.Ds μ (sd.D μ x)

theorem inner_Lap (x y : V) : ⟪x, sd.Lap y⟫ = ∑ μ, ⟪sd.D μ x, sd.D μ y⟫ := by
  unfold Lap
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [inner_D]

theorem Lap_selfadj (x y : V) : ⟪sd.Lap x, y⟫ = ⟪x, sd.Lap y⟫ := by
  rw [inner_Lap, ← inner_conj_symm, inner_Lap]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [inner_conj_symm]


theorem inner_Ds_Ds (w : Fin 3 → V) (μ ν : Fin 3) :
    ⟪sd.Ds μ (w μ), sd.Ds ν (w ν)⟫ = ⟪sd.D ν (w μ), sd.D μ (w ν)⟫ := by
  rw [inner_Ds, ← sd.Ds_D, ← inner_D]

/-- Weitzenböck identity (flat, twisted cell). -/
theorem weitzenbock (w : Fin 3 → V) :
    (1 / 2 : ℝ) * ∑ μ, ∑ ν, ‖sd.D μ (w ν) - sd.D ν (w μ)‖ ^ 2 + ‖∑ μ, sd.Ds μ (w μ)‖ ^ 2
      = ∑ μ, ∑ ν, ‖sd.D ν (w μ)‖ ^ 2 := by
  have hcurl : ∀ μ ν, ‖sd.D μ (w ν) - sd.D ν (w μ)‖ ^ 2
      = ‖sd.D μ (w ν)‖ ^ 2 - 2 * RCLike.re ⟪sd.D μ (w ν), sd.D ν (w μ)⟫ + ‖sd.D ν (w μ)‖ ^ 2 :=
    fun μ ν => norm_sub_sq (𝕜 := ℂ) _ _
  simp only [hcurl, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hA : ∑ μ, ∑ ν, ‖sd.D μ (w ν)‖ ^ 2 = ∑ μ, ∑ ν, ‖sd.D ν (w μ)‖ ^ 2 := Finset.sum_comm
  have hdiv : ‖∑ μ, sd.Ds μ (w μ)‖ ^ 2 = ∑ μ, ∑ ν, RCLike.re ⟪sd.D μ (w ν), sd.D ν (w μ)⟫ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sum]
    simp only [sum_inner, map_sum]
    refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
    rw [sd.inner_Ds_Ds w ν μ]
  rw [hdiv, hA]
  ring

#print axioms weitzenbock

/-- the linear map underlying `S μ` -/
noncomputable def Sl (μ : Fin 3) : Module.End ℂ V := (sd.S μ).toLinearEquiv.toLinearMap

theorem Sl_apply (μ : Fin 3) (x : V) : sd.Sl μ x = sd.S μ x := rfl

theorem Sl_pow_apply (μ : Fin 3) (m : ℕ) (x : V) : (sd.Sl μ ^ m) x = (sd.S μ)^[m] x := by
  rw [Module.End.pow_apply]; rfl

theorem iter_sub (μ : Fin 3) (m : ℕ) (x y : V) :
    (sd.S μ)^[m] (x - y) = (sd.S μ)^[m] x - (sd.S μ)^[m] y := by
  rw [← sd.Sl_pow_apply, ← sd.Sl_pow_apply, ← sd.Sl_pow_apply, map_sub]

/-- the mass pairing `⟨ε, Σ_{i<n} S^i x⟩` -/
noncomputable def Qm (μ : Fin 3) (x : V) : ℂ := ⟪sd.eps, ∑ i ∈ Finset.range sd.n, (sd.S μ)^[i] x⟫

theorem tele (μ : Fin 3) (ν : V) (m : ℕ) :
    ∑ i ∈ Finset.range m, (sd.S μ)^[i] (sd.D μ ν) = (sd.S μ)^[m] ν - ν := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      unfold D
      rw [sd.iter_sub, Function.iterate_succ_apply]
      abel

theorem Qm_D (μ : Fin 3) (ν : V) : sd.Qm μ (sd.D μ ν) = (sd.ph μ - 1) * ⟪sd.eps, ν⟫ := by
  unfold Qm
  rw [sd.tele, sd.Spow, inner_sub_right, inner_smul_right]
  ring


/-- divergence -/
def Dstar (w : Fin 3 → V) : V := ∑ μ, sd.Ds μ (w μ)

theorem fixed_zero (μ : Fin 3) (h : sd.ph μ ≠ 1) (x : V) (hx : sd.S μ x = x) : x = 0 := by
  have h1 : (sd.S μ)^[sd.n] x = x := Function.iterate_fixed hx sd.n
  rw [sd.Spow] at h1
  have h2 : (sd.ph μ - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) h
  · exact h3

theorem D_eq_zero_iff (μ : Fin 3) (x : V) : sd.D μ x = 0 ↔ sd.S μ x = x := by
  unfold D; exact sub_eq_zero

theorem norm_sum_eq_zero {ι : Type*} [Fintype ι] (x : ι → V) (h : ∑ i, ‖x i‖ ^ 2 = 0) : ∀ i, x i = 0 := by
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h i (Finset.mem_univ i)
  exact norm_eq_zero.mp (by simpa using this)

theorem Lap_eq_zero (u : V) (hu : sd.Lap u = 0) : ∀ μ, sd.S μ u = u := by
  have h1 : ⟪u, sd.Lap u⟫ = 0 := by rw [hu]; simp
  rw [inner_Lap] at h1
  have h2 : ∑ μ, ‖sd.D μ u‖ ^ 2 = 0 := by
    have h3 := congrArg Complex.re h1
    simp only [Complex.re_sum, Complex.zero_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  intro μ
  exact (sd.D_eq_zero_iff μ u).mp (norm_sum_eq_zero (fun μ => sd.D μ u) h2 μ)

theorem eps_inner_ne : ⟪sd.eps, sd.eps⟫ ≠ 0 := fun h => sd.eps_ne (inner_self_eq_zero.mp h)


theorem D_add (μ : Fin 3) (x y : V) : sd.D μ (x + y) = sd.D μ x + sd.D μ y := by
  unfold D; rw [map_add]; abel
theorem D_sub (μ : Fin 3) (x y : V) : sd.D μ (x - y) = sd.D μ x - sd.D μ y := by
  unfold D; rw [map_sub]; abel
theorem Ds_sub (μ : Fin 3) (x y : V) : sd.Ds μ (x - y) = sd.Ds μ x - sd.Ds μ y := by
  unfold Ds; rw [map_sub]; abel
theorem D_smul (μ : Fin 3) (c : ℂ) (x : V) : sd.D μ (c • x) = c • sd.D μ x := by
  unfold D; rw [map_smul, smul_sub]
theorem Ds_add (μ : Fin 3) (x y : V) : sd.Ds μ (x + y) = sd.Ds μ x + sd.Ds μ y := by
  unfold Ds; rw [map_add]; abel
theorem Ds_smul (μ : Fin 3) (c : ℂ) (x : V) : sd.Ds μ (c • x) = c • sd.Ds μ x := by
  unfold Ds; rw [map_smul, smul_sub]
theorem Lap_add (x y : V) : sd.Lap (x + y) = sd.Lap x + sd.Lap y := by
  unfold Lap; simp only [D_add, Ds_add, Finset.sum_add_distrib]
theorem Lap_smul (c : ℂ) (x : V) : sd.Lap (c • x) = c • sd.Lap x := by
  unfold Lap; simp only [D_smul, Ds_smul, Finset.smul_sum]
theorem Lap_sub (x y : V) : sd.Lap (x - y) = sd.Lap x - sd.Lap y := by
  have : x - y = x + (-1 : ℂ) • y := by rw [neg_smul, one_smul, sub_eq_add_neg]
  rw [this, Lap_add, Lap_smul]; simp [sub_eq_add_neg]

/-- the Laplacian as a linear map -/
noncomputable def LapL : V →ₗ[ℂ] V where
  toFun := sd.Lap
  map_add' := sd.Lap_add
  map_smul' := sd.Lap_smul

theorem Lap_inj (μ0 : Fin 3) (h : sd.ph μ0 ≠ 1) (u : V) (hu : sd.Lap u = 0) : u = 0 :=
  sd.fixed_zero μ0 h u (sd.Lap_eq_zero u hu μ0)


theorem Lap_surj [FiniteDimensional ℂ V] (μ0 : Fin 3) (h : sd.ph μ0 ≠ 1) (y : V) : ∃ x, sd.Lap x = y := by
  have hinj : Function.Injective sd.LapL := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    exact sd.Lap_inj μ0 h u hu
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hinj) y
  exact ⟨x, hx⟩

/-- Step A of positivity: `Lap g ∈ span ε` -/
theorem Lap_g_eq (w : Fin 3 → V)
    (hK : ∀ u, ⟪sd.eps, u⟫ = 0 → ⟪sd.Dstar w, sd.Lap u⟫ = 0) :
    ∃ c : ℂ, sd.Lap (sd.Dstar w) = c • sd.eps := by
  set g := sd.Dstar w with hg
  set c : ℂ := ⟪sd.eps, sd.Lap g⟫ / ⟪sd.eps, sd.eps⟫ with hc
  refine ⟨c, ?_⟩
  set u := sd.Lap g - c • sd.eps with hu
  have hne := sd.eps_inner_ne
  have h0 : ⟪sd.eps, u⟫ = 0 := by
    rw [hu, inner_sub_right, inner_smul_right, hc]
    field_simp
    ring
  have h1 := hK u h0
  rw [← sd.Lap_selfadj] at h1
  have h2 : ⟪sd.Lap g, u⟫ = ⟪u, u⟫ := by
    have : sd.Lap g = u + c • sd.eps := by rw [hu]; abel
    rw [this, inner_add_left, inner_smul_left, h0]
    simp
  rw [h2] at h1
  have : u = 0 := inner_self_eq_zero.mp h1
  rw [hu] at this
  exact sub_eq_zero.mp this


theorem grad_zero (w : Fin 3 → V) (hcurl : ∀ μ ν, sd.D μ (w ν) = sd.D ν (w μ))
    (hdiv : sd.Dstar w = 0) : ∀ μ ν, sd.D ν (w μ) = 0 := by
  have h := sd.weitzenbock w
  have h1 : ∀ μ ν, sd.D μ (w ν) - sd.D ν (w μ) = 0 := fun μ ν => by rw [hcurl μ ν]; simp
  simp only [h1, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    mul_zero, zero_add] at h
  unfold Dstar at hdiv
  rw [hdiv, norm_zero] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  intro μ ν
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ∑ j, ‖sd.D j (w i)‖ ^ 2 :=
    fun i _ => Finset.sum_nonneg (fun j _ => by positivity)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h.symm μ (Finset.mem_univ μ)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h2 ν (Finset.mem_univ ν)
  exact norm_eq_zero.mp (by simpa using h3)


/-- **POINTWISE POSITIVITY OF THE SYMBOL** (abstract). -/
theorem symbol_positive [FiniteDimensional ℂ V] (w : Fin 3 → V)
    (hcurl : ∀ μ ν, sd.D μ (w ν) = sd.D ν (w μ))
    (hQ : ∀ μ, sd.Qm μ (w μ) = 0)
    (hK : ∀ u, ⟪sd.eps, u⟫ = 0 → ⟪sd.Dstar w, sd.Lap u⟫ = 0) : ∀ μ, w μ = 0 := by
  obtain ⟨c, hLg⟩ := sd.Lap_g_eq w hK
  set g := sd.Dstar w with hg
  have hne := sd.eps_inner_ne
  by_cases hall : ∀ μ, sd.ph μ = 1
  · -- trivial phases
    have hLeps : sd.Lap sd.eps = 0 := by
      unfold Lap
      refine Finset.sum_eq_zero (fun μ _ => ?_)
      have : sd.D μ sd.eps = 0 := (sd.D_eq_zero_iff μ _).mpr (sd.eps_fixed hall μ)
      rw [this]; unfold Ds; simp
    have hc0 : c = 0 := by
      have h1 : ⟪sd.eps, sd.Lap g⟫ = 0 := by
        rw [← sd.Lap_selfadj, hLeps]; simp
      rw [hLg, inner_smul_right] at h1
      exact (mul_eq_zero.mp h1).resolve_right hne
    rw [hc0, zero_smul] at hLg
    have hgfix := sd.Lap_eq_zero g hLg
    obtain ⟨c', hc'⟩ := sd.fixed_span hall g hgfix
    have hc'0 : c' = 0 := by
      have h1 : ⟪sd.eps, g⟫ = 0 := by
        rw [hg, Dstar, inner_sum]
        refine Finset.sum_eq_zero (fun μ _ => ?_)
        rw [← sd.inner_D]
        have : sd.D μ sd.eps = 0 := (sd.D_eq_zero_iff μ _).mpr (sd.eps_fixed hall μ)
        rw [this]; simp
      rw [hc', inner_smul_right] at h1
      exact (mul_eq_zero.mp h1).resolve_right hne
    rw [hc'0, zero_smul] at hc'
    have hdiv : sd.Dstar w = 0 := hc'
    have hgr := sd.grad_zero w hcurl hdiv
    intro μ
    obtain ⟨cμ, hcμ⟩ := sd.fixed_span hall (w μ) (fun ν => (sd.D_eq_zero_iff ν _).mp (hgr μ ν))
    have h1 := hQ μ
    rw [hcμ] at h1
    unfold Qm at h1
    have hfix : sd.S μ (cμ • sd.eps) = cμ • sd.eps := by rw [map_smul, sd.eps_fixed hall μ]
    have hit : ∀ i : ℕ, (sd.S μ)^[i] (cμ • sd.eps) = cμ • sd.eps := fun i => Function.iterate_fixed hfix i
    simp only [hit, Finset.sum_const, Finset.card_range] at h1
    have hn : (sd.n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr sd.hn.ne'
    have h2 : (sd.n : ℂ) * (cμ * ⟪sd.eps, sd.eps⟫) = 0 := by
      have := h1
      rw [← Nat.cast_smul_eq_nsmul ℂ, inner_smul_right, inner_smul_right] at this
      exact this
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hn
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · rw [hcμ, h4, zero_smul]
      · exact absurd h4 hne
  · push_neg at hall
    obtain ⟨μ0, hμ0⟩ := hall
    obtain ⟨a, ha⟩ := sd.Lap_surj μ0 hμ0 sd.eps
    obtain ⟨ν, hν⟩ := sd.Lap_surj μ0 hμ0 g
    -- g = c • a
    have hga : g = c • a := by
      have h0 : sd.Lap (g - c • a) = 0 := by rw [sd.Lap_sub, sd.Lap_smul, hLg, ha, sub_self]
      have := sd.Lap_inj μ0 hμ0 _ h0
      exact sub_eq_zero.mp this
    -- w' = w - D ν is curl free and divergence free
    set w' : Fin 3 → V := fun μ => w μ - sd.D μ ν with hw'
    have hcurl' : ∀ μ ν', sd.D μ (w' ν') = sd.D ν' (w' μ) := by
      intro μ ν'
      simp only [hw', sd.D_sub]
      rw [hcurl μ ν', sd.D_D μ ν']
    have hdiv' : sd.Dstar w' = 0 := by
      have : sd.Dstar w' = g - sd.Lap ν := by
        simp only [hw', Dstar, sd.Ds_sub, Finset.sum_sub_distrib]
        rfl
      rw [this, hν, sub_self]
    have hgr := sd.grad_zero w' hcurl' hdiv'
    have hw0 : ∀ μ, w μ = sd.D μ ν := by
      intro μ
      have : w' μ = 0 := sd.fixed_zero μ0 hμ0 _ ((sd.D_eq_zero_iff μ0 _).mp (hgr μ μ0))
      have h2 : w μ - sd.D μ ν = 0 := this
      exact sub_eq_zero.mp h2
    have hεν : ⟪sd.eps, ν⟫ = 0 := by
      have h1 := hQ μ0
      rw [hw0 μ0, sd.Qm_D] at h1
      exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hμ0)
    have ha0 : a ≠ 0 := by
      intro h0
      apply sd.eps_ne
      rw [← ha, h0]
      unfold Lap
      simp [Ds, D]
    have hc0 : c = 0 := by
      have h1 : ⟪sd.eps, ν⟫ = c * ⟪a, a⟫ := by
        rw [← ha, sd.Lap_selfadj, hν, hga, inner_smul_right]
      rw [hεν] at h1
      have h2 : ⟪a, a⟫ ≠ 0 := fun h => ha0 (inner_self_eq_zero.mp h)
      exact (mul_eq_zero.mp h1.symm).resolve_right h2
    have hg0 : g = 0 := by rw [hga, hc0, zero_smul]
    have hν0 : ν = 0 := sd.Lap_inj μ0 hμ0 _ (by rw [hν, hg0])
    intro μ
    rw [hw0 μ, hν0]
    unfold D; simp

end SymData

end Abstract

#print axioms AdalyFormal.FlatCoercivity.SymData.symbol_positive
#print axioms AdalyFormal.FlatCoercivity.SymData.Qm_D
#print axioms AdalyFormal.FlatCoercivity.SymData.Lap_surj

end AdalyFormal.FlatCoercivity
