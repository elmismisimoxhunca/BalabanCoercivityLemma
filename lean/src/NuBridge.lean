import NuMono1

/-!
# NuBridge -- from a pencil on the fixed space of a reflection to the full-space monotone lemma (lane ncwdh_ell2_20261018)

`TE` (on `E`) and `TF` (on `F`) are self-adjoint involutions (reflections); `P = (1 + TE)/2` is the orthogonal projection onto the fixed space of `TE`.
Operators `A w` (symmetric, commuting with `TE`) agree on the fixed space with the pencil `H0 + w B`;  `Q w` agree with a fixed `Q0` on the fixed space and
intertwine `TE`, `TF`.  Then `w ↦ ⟨y, (Q A⁻¹ Q*)⁻¹ y⟩` is monotone for `TF`-fixed `y`, on intervals where `A w` and `N w = Q A⁻¹ Q*` are units.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AdalyNcwdhTwo.Bridge

open scoped RealInnerProductSpace
open AdalyNcwdhTwo.Mono

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- the projection onto the fixed space of `TE`. -/
noncomputable def Pr (TE : E →L[ℝ] E) : E →L[ℝ] E := (1 / 2 : ℝ) • (1 + TE)

theorem Pr_apply (TE : E →L[ℝ] E) (x : E) : Pr TE x = (1 / 2 : ℝ) • (x + TE x) := by
  simp [Pr]

theorem Pr_sym {TE : E →L[ℝ] E} (hT : Sym TE) : Sym (Pr TE) := by
  intro a b
  simp only [Pr_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hT a b]
  simp

theorem Pr_idem {TE : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (x : E) : Pr TE (Pr TE x) = Pr TE x := by
  simp only [Pr_apply, map_smul, map_add, hT2]
  module

theorem Pr_fixed {TE : E →L[ℝ] E} {x : E} (hx : TE x = x) : Pr TE x = x := by
  rw [Pr_apply, hx]; module

theorem TE_Pr {TE : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (x : E) : TE (Pr TE x) = Pr TE x := by
  simp only [Pr_apply, map_smul, map_add, hT2]
  rw [add_comm]

/-- an operator commuting with `TE` commutes with `Pr TE`. -/
theorem Pr_comm {TE A : E →L[ℝ] E} (h : ∀ x, A (TE x) = TE (A x)) (x : E) : A (Pr TE x) = Pr TE (A x) := by
  simp only [Pr_apply, map_smul, map_add, h]


/-- if `S` is a two-sided inverse of `T` then `Ring.inverse T = S`. -/
theorem ringInverse_eq {R : Type*} [Ring R] {T S : R} (h1 : T * S = 1) (h2 : S * T = 1) : Ring.inverse T = S := by
  have hu : IsUnit T := ⟨⟨T, S, h1, h2⟩, rfl⟩
  calc Ring.inverse T = Ring.inverse T * (T * S) := by rw [h1, mul_one]
    _ = (Ring.inverse T * T) * S := by rw [mul_assoc]
    _ = S := by rw [Ring.inverse_mul_cancel T hu, one_mul]

/-- ring identity: `(X P + (1-P)) (Y P + (1-P)) = 1` for an idempotent `P` commuting with `X, Y` and `X Y = 1`. -/
theorem ring_aux {R : Type*} [Ring R] (X Y P : R) (hPP : P * P = P) (hXP : X * P = P * X) (hYP : Y * P = P * Y)
    (hXY : X * Y = 1) : (X * P + (1 - P)) * (Y * P + (1 - P)) = 1 := by
  have e : (X * P + (1 - P)) * (Y * P + (1 - P)) =
      X * P * (Y * P) + X * P * (1 - P) + (1 - P) * (Y * P) + (1 - P) * (1 - P) := by noncomm_ring
  have h1 : X * P * (Y * P) = P := by
    calc X * P * (Y * P) = X * (P * (Y * P)) := by rw [mul_assoc]
      _ = X * (P * (P * Y)) := by rw [← hYP]
      _ = X * ((P * P) * Y) := by rw [mul_assoc]
      _ = X * (P * Y) := by rw [hPP]
      _ = X * (Y * P) := by rw [hYP]
      _ = (X * Y) * P := by rw [mul_assoc]
      _ = P := by rw [hXY, one_mul]
  have h2 : X * P * (1 - P) = 0 := by
    calc X * P * (1 - P) = X * P - X * (P * P) := by noncomm_ring
      _ = 0 := by rw [hPP, sub_self]
  have h3 : (1 - P) * (Y * P) = 0 := by
    calc (1 - P) * (Y * P) = Y * P - P * (Y * P) := by noncomm_ring
      _ = Y * P - (P * Y) * P := by rw [mul_assoc]
      _ = Y * P - (Y * P) * P := by rw [← hYP]
      _ = Y * P - Y * (P * P) := by rw [mul_assoc]
      _ = 0 := by rw [hPP, sub_self]
  have h4 : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPP]; abel
  rw [e, h1, h2, h3, h4]
  abel

/-- `A P + (1 - P)` is a unit when `A` is a unit commuting with the projection `P`. -/
theorem hhat_inverse {TE A : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (hAc : ∀ x, A (TE x) = TE (A x)) (hA : IsUnit A) :
    Ring.inverse (A * Pr TE + (1 - Pr TE)) = Ring.inverse A * Pr TE + (1 - Pr TE) := by
  have hGc : ∀ x, Ring.inverse A (TE x) = TE (Ring.inverse A x) := by
    intro x
    have h1 : ∀ z, A (Ring.inverse A z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.mul_inverse_cancel A hA)
    have h2 : ∀ z, Ring.inverse A (A z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.inverse_mul_cancel A hA)
    calc Ring.inverse A (TE x) = Ring.inverse A (TE (A (Ring.inverse A x))) := by rw [h1]
      _ = Ring.inverse A (A (TE (Ring.inverse A x))) := by rw [hAc]
      _ = TE (Ring.inverse A x) := h2 _
  have hPP : Pr TE * Pr TE = Pr TE := by ext x; exact Pr_idem hT2 x
  have hAP : A * Pr TE = Pr TE * A := by
    ext x; simp only [ContinuousLinearMap.mul_apply]; exact Pr_comm hAc x
  have hGP : Ring.inverse A * Pr TE = Pr TE * Ring.inverse A := by
    ext x; simp only [ContinuousLinearMap.mul_apply]; exact Pr_comm hGc x
  have hAG : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel A hA
  have hGA : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel A hA
  apply ringInverse_eq
  · exact ring_aux A (Ring.inverse A) (Pr TE) hPP hAP hGP hAG
  · exact ring_aux (Ring.inverse A) A (Pr TE) hPP hGP hAP hGA

/-- the pencil on the whole space built from the fixed-space pencil. -/
noncomputable def H0' (TE H0 : E →L[ℝ] E) : E →L[ℝ] E := H0 * Pr TE + (1 - Pr TE)
noncomputable def B' (TE B : E →L[ℝ] E) : E →L[ℝ] E := B * Pr TE

theorem Hc_eq {TE H0 B A : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) {w : ℝ}
    (hAff : ∀ x, TE x = x → A x = H0 x + w • B x) :
    Hc (H0' TE H0) (B' TE B) w = A * Pr TE + (1 - Pr TE) := by
  ext x
  have h := hAff (Pr TE x) (TE_Pr hT2 x)
  simp only [Hc, H0', B', ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [h]
  abel

theorem H0'_sym {TE H0 : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (hTs : Sym TE) (hH0 : Sym H0)
    (hH0c : ∀ x, H0 (TE x) = TE (H0 x)) : Sym (H0' TE H0) := by
  intro a b
  have hPs := Pr_sym hTs
  have e1 : ⟪H0 (Pr TE a), b⟫ = ⟪a, H0 (Pr TE b)⟫ := by
    rw [hH0 (Pr TE a) b, hPs a (H0 b), Pr_comm hH0c b]
  have e2 : ⟪Pr TE a, b⟫ = ⟪a, Pr TE b⟫ := hPs a b
  simp only [H0', ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, e1, e2]

theorem B'_sym {TE B : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (hTs : Sym TE) (hB : Sym B)
    (hBc : ∀ x, B (TE x) = TE (B x)) : Sym (B' TE B) := by
  intro a b
  have hPs := Pr_sym hTs
  have e1 : ⟪B (Pr TE a), b⟫ = ⟪a, B (Pr TE b)⟫ := by
    rw [hB (Pr TE a) b, hPs a (B b), Pr_comm hBc b]
  simpa only [B', ContinuousLinearMap.mul_apply] using e1

theorem B'_psd {TE B : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (hTs : Sym TE) (hBpsd : ∀ a, 0 ≤ ⟪a, B a⟫)
    (hBc : ∀ x, B (TE x) = TE (B x)) (a : E) : 0 ≤ ⟪a, B' TE B a⟫ := by
  have hPs := Pr_sym hTs
  have h1 : ⟪a, B (Pr TE a)⟫ = ⟪Pr TE a, B (Pr TE a)⟫ := by
    have e : B (Pr TE a) = Pr TE (B (Pr TE a)) := by
      rw [← Pr_comm hBc, Pr_idem hT2]
    calc ⟪a, B (Pr TE a)⟫ = ⟪a, Pr TE (B (Pr TE a))⟫ := by rw [← e]
      _ = ⟪Pr TE a, B (Pr TE a)⟫ := (hPs a _).symm
  simp only [B', ContinuousLinearMap.mul_apply]
  rw [h1]
  exact hBpsd _

theorem TE_decomp {TE : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (x : E) :
    TE (x - Pr TE x) = -(x - Pr TE x) := by
  rw [map_sub, TE_Pr hT2, Pr_apply]
  module

theorem fixed_antifixed_zero {TE : E →L[ℝ] E} {u v : E} (hu : TE u = u) (hv : TE v = -v) (h : u + v = 0) : u = 0 ∧ v = 0 := by
  have h1 : TE (u + v) = 0 := by rw [h, map_zero]
  rw [map_add, hu, hv] at h1
  have h2 : u = 0 := by
    have : (2 : ℝ) • u = 0 := by
      calc (2 : ℝ) • u = (u + v) + (u + -v) := by module
        _ = 0 := by rw [h, h1]; simp
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  refine ⟨h2, ?_⟩
  rw [h2, zero_add] at h
  exact h

end

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

theorem Nhat_unit {TE : E →L[ℝ] E} {TF : F →L[ℝ] F} (hTE2 : ∀ x, TE (TE x) = x) (hTF2 : ∀ y, TF (TF y) = y)
    (Q0 : E →L[ℝ] F) (Q0s : F →L[ℝ] E) (hQ0 : ∀ x y, ⟪Q0 x, y⟫ = ⟪x, Q0s y⟫)
    (hQ0c : ∀ x, Q0 (TE x) = TF (Q0 x)) (hQ0sc : ∀ y, Q0s (TF y) = TE (Q0s y))
    (hinj : ∀ y, Q0s y = 0 → y = 0)
    {A : E →L[ℝ] E} (hAc : ∀ x, A (TE x) = TE (A x)) (hA : IsUnit A) {Nw : F →L[ℝ] F}
    (hNfix : ∀ y, TF y = y → Nw y = Q0 (Ring.inverse A (Q0s y))) (hNunit : IsUnit Nw) :
    IsUnit (Q0.comp ((Ring.inverse (A * Pr TE + (1 - Pr TE))).comp Q0s)) := by
  rw [hhat_inverse hTE2 hAc hA]
  set M : F →L[ℝ] F := Q0.comp ((Ring.inverse A * Pr TE + (1 - Pr TE)).comp Q0s) with hM
  have hGc : ∀ x, Ring.inverse A (TE x) = TE (Ring.inverse A x) := by
    intro x
    have h1 : ∀ z, A (Ring.inverse A z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.mul_inverse_cancel A hA)
    have h2 : ∀ z, Ring.inverse A (A z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.inverse_mul_cancel A hA)
    calc Ring.inverse A (TE x) = Ring.inverse A (TE (A (Ring.inverse A x))) := by rw [h1]
      _ = Ring.inverse A (A (TE (Ring.inverse A x))) := by rw [hAc]
      _ = TE (Ring.inverse A x) := h2 _
  have hNinj : ∀ y, Nw y = 0 → y = 0 := by
    intro y hy
    obtain ⟨u, hu⟩ := hNunit
    have : (↑u⁻¹ : F →L[ℝ] F) (Nw y) = y := by
      rw [← hu]
      exact congrArg (fun S : F →L[ℝ] F => S y) (Units.inv_mul u)
    rw [hy] at this
    simpa using this.symm
  -- action of M on fixed / anti-fixed vectors
  have hMfix : ∀ y, TF y = y → M y = Q0 (Ring.inverse A (Q0s y)) := by
    intro y hy
    have hs : TE (Q0s y) = Q0s y := by rw [← hQ0sc, hy]
    simp only [hM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [Pr_fixed hs]
    simp
  have hManti : ∀ y, TF y = -y → M y = Q0 (Q0s y) := by
    intro y hy
    have hs : TE (Q0s y) = -(Q0s y) := by rw [← hQ0sc, hy, map_neg]
    have hP0 : Pr TE (Q0s y) = 0 := by rw [Pr_apply, hs]; simp
    simp only [hM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [hP0]
    simp
  have hMinj : ∀ y, M y = 0 → y = 0 := by
    intro y hy
    set y1 := Pr TF y with hy1
    set y2 := y - Pr TF y with hy2
    have hy1f : TF y1 = y1 := TE_Pr hTF2 y
    have hy2f : TF y2 = -y2 := TE_decomp hTF2 y
    have hsplit : y = y1 + y2 := by rw [hy1, hy2]; abel
    have hM1 : TF (M y1) = M y1 := by
      rw [hMfix y1 hy1f]
      have : TE (Ring.inverse A (Q0s y1)) = Ring.inverse A (Q0s y1) := by
        rw [← hGc, ← hQ0sc, hy1f]
      rw [← hQ0c, this]
    have hM2 : TF (M y2) = -(M y2) := by
      rw [hManti y2 hy2f, ← hQ0c, ← hQ0sc, hy2f, map_neg, map_neg]
    have hsum : M y1 + M y2 = 0 := by rw [← map_add, ← hsplit]; exact hy
    obtain ⟨h1z, h2z⟩ := fixed_antifixed_zero hM1 hM2 hsum
    have e1 : y1 = 0 := by
      apply hNinj
      rw [hNfix y1 hy1f, ← hMfix y1 hy1f]; exact h1z
    have e2 : y2 = 0 := by
      rw [hManti y2 hy2f] at h2z
      have : ⟪Q0s y2, Q0s y2⟫ = 0 := by
        rw [← hQ0, h2z]; simp
      exact hinj y2 (inner_self_eq_zero.mp this)
    rw [hsplit, e1, e2, add_zero]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj' : Function.Injective M := by
    intro a b hab
    have : M (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hMinj _ this)
  refine ⟨hinj', ?_⟩
  exact (LinearMap.injective_iff_surjective (f := (M : F →ₗ[ℝ] F))).mp hinj'

theorem Nhat_apply_fixed {TE : E →L[ℝ] E} {TF : F →L[ℝ] F} (hTE2 : ∀ x, TE (TE x) = x)
    (Q0 : E →L[ℝ] F) (Q0s : F →L[ℝ] E) (hQ0sc : ∀ y, Q0s (TF y) = TE (Q0s y))
    {A : E →L[ℝ] E} (hAc : ∀ x, A (TE x) = TE (A x)) (hA : IsUnit A) {y : F} (hy : TF y = y) :
    (Q0.comp ((Ring.inverse (A * Pr TE + (1 - Pr TE))).comp Q0s)) y = Q0 (Ring.inverse A (Q0s y)) := by
  rw [hhat_inverse hTE2 hAc hA]
  have hs : TE (Q0s y) = Q0s y := by rw [← hQ0sc, hy]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [Pr_fixed hs]
  simp

theorem hhat_isUnit {TE A : E →L[ℝ] E} (hT2 : ∀ x, TE (TE x) = x) (hAc : ∀ x, A (TE x) = TE (A x)) (hA : IsUnit A) :
    IsUnit (A * Pr TE + (1 - Pr TE)) := by
  have hGc : ∀ x, Ring.inverse A (TE x) = TE (Ring.inverse A x) := by
    intro x
    have h1 : ∀ z, A (Ring.inverse A z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.mul_inverse_cancel A hA)
    have h2 : ∀ z, Ring.inverse A (A z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.inverse_mul_cancel A hA)
    calc Ring.inverse A (TE x) = Ring.inverse A (TE (A (Ring.inverse A x))) := by rw [h1]
      _ = Ring.inverse A (A (TE (Ring.inverse A x))) := by rw [hAc]
      _ = TE (Ring.inverse A x) := h2 _
  have hPP : Pr TE * Pr TE = Pr TE := by ext x; exact Pr_idem hT2 x
  have hAP : A * Pr TE = Pr TE * A := by
    ext x; simp only [ContinuousLinearMap.mul_apply]; exact Pr_comm hAc x
  have hGP : Ring.inverse A * Pr TE = Pr TE * Ring.inverse A := by
    ext x; simp only [ContinuousLinearMap.mul_apply]; exact Pr_comm hGc x
  have hAG : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel A hA
  have hGA : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel A hA
  exact ⟨⟨_, Ring.inverse A * Pr TE + (1 - Pr TE), ring_aux A (Ring.inverse A) (Pr TE) hPP hAP hGP hAG,
    ring_aux (Ring.inverse A) A (Pr TE) hPP hGP hAP hGA⟩, rfl⟩

end

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

theorem monotone_bridge
    {TE : E →L[ℝ] E} {TF : F →L[ℝ] F} (hTE2 : ∀ x, TE (TE x) = x) (hTEs : Sym TE)
    (hTF2 : ∀ y, TF (TF y) = y)
    {H0 B : E →L[ℝ] E} (hH0s : Sym H0) (hBs : Sym B) (hBpsd : ∀ a, 0 ≤ ⟪a, B a⟫)
    (hH0c : ∀ x, H0 (TE x) = TE (H0 x)) (hBc : ∀ x, B (TE x) = TE (B x))
    (Q0 : E →L[ℝ] F) (Q0s : F →L[ℝ] E) (hQ0 : ∀ x y, ⟪Q0 x, y⟫ = ⟪x, Q0s y⟫)
    (hQ0c : ∀ x, Q0 (TE x) = TF (Q0 x)) (hQ0sc : ∀ y, Q0s (TF y) = TE (Q0s y)) (hinj : ∀ y, Q0s y = 0 → y = 0)
    (A : ℝ → E →L[ℝ] E) (Q : ℝ → E →L[ℝ] F) (Qs : ℝ → F →L[ℝ] E) {lo hi : ℝ}
    (hAc : ∀ w ∈ Set.Icc lo hi, ∀ x, A w (TE x) = TE (A w x))
    (hAff : ∀ w ∈ Set.Icc lo hi, ∀ x, TE x = x → A w x = H0 x + w • B x)
    (hQ : ∀ w ∈ Set.Icc lo hi, ∀ x, TE x = x → Q w x = Q0 x)
    (hQs : ∀ w ∈ Set.Icc lo hi, ∀ y, TF y = y → Qs w y = Q0s y)
    (hQc : ∀ w ∈ Set.Icc lo hi, ∀ x, Q w (TE x) = TF (Q w x))
    (hQsc : ∀ w ∈ Set.Icc lo hi, ∀ y, Qs w (TF y) = TE (Qs w y))
    (hunit : ∀ w ∈ Set.Icc lo hi, IsUnit (A w) ∧ IsUnit ((Q w).comp ((Ring.inverse (A w)).comp (Qs w))))
    (y : F) (hy : TF y = y) :
    MonotoneOn (fun w => ⟪y, Ring.inverse ((Q w).comp ((Ring.inverse (A w)).comp (Qs w))) y⟫) (Set.Icc lo hi) := by
  have hQ0s_fix : ∀ y, TF y = y → TE (Q0s y) = Q0s y := fun y hy => by rw [← hQ0sc, hy]
  -- facts at each w
  have key : ∀ w ∈ Set.Icc lo hi,
      Hc (H0' TE H0) (B' TE B) w = A w * Pr TE + (1 - Pr TE) := fun w hw => Hc_eq hTE2 (hAff w hw)
  have hGc : ∀ w ∈ Set.Icc lo hi, ∀ x, Ring.inverse (A w) (TE x) = TE (Ring.inverse (A w) x) := by
    intro w hw x
    have hA := (hunit w hw).1
    have h1 : ∀ z, A w (Ring.inverse (A w) z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.mul_inverse_cancel (A w) hA)
    have h2 : ∀ z, Ring.inverse (A w) (A w z) = z := fun z =>
      congrArg (fun S : E →L[ℝ] E => S z) (Ring.inverse_mul_cancel (A w) hA)
    calc Ring.inverse (A w) (TE x) = Ring.inverse (A w) (TE (A w (Ring.inverse (A w) x))) := by rw [h1]
      _ = Ring.inverse (A w) (A w (TE (Ring.inverse (A w) x))) := by rw [hAc w hw]
      _ = TE (Ring.inverse (A w) x) := h2 _
  have hNfix : ∀ w ∈ Set.Icc lo hi, ∀ y', TF y' = y' →
      ((Q w).comp ((Ring.inverse (A w)).comp (Qs w))) y' = Q0 (Ring.inverse (A w) (Q0s y')) := by
    intro w hw y' hy'
    simp only [ContinuousLinearMap.comp_apply]
    rw [hQs w hw y' hy', hQ w hw _ (by rw [← hGc w hw, hQ0s_fix y' hy'])]
  have hNunit' : ∀ w ∈ Set.Icc lo hi, IsUnit (Nc (H0' TE H0) (B' TE B) Q0 Q0s w) := by
    intro w hw
    have := Nhat_unit hTE2 hTF2 Q0 Q0s hQ0 hQ0c hQ0sc hinj (hAc w hw) (hunit w hw).1 (hNfix w hw) (hunit w hw).2
    simp only [Nc, key w hw]
    exact this
  have hmono := monotoneOn_phi (H0' TE H0) (B' TE B) Q0 Q0s y (lo := lo) (hi := hi)
    (fun w hw => ⟨by rw [key w hw]; exact hhat_isUnit hTE2 (hAc w hw) (hunit w hw).1, hNunit' w hw⟩)
    (H0'_sym hTE2 hTEs hH0s hH0c) (B'_sym hTE2 hTEs hBs hBc) (B'_psd hTE2 hTEs hBpsd hBc) hQ0
  refine hmono.congr ?_
  intro w hw
  show ⟪y, Ring.inverse (Nc (H0' TE H0) (B' TE B) Q0 Q0s w) y⟫ = _
  have hA := (hunit w hw).1
  have hNw := (hunit w hw).2
  set N : F →L[ℝ] F := (Q w).comp ((Ring.inverse (A w)).comp (Qs w)) with hN
  set Nh : F →L[ℝ] F := Nc (H0' TE H0) (B' TE B) Q0 Q0s w with hNh
  have hNhdef : Nh = Q0.comp ((Ring.inverse (A w * Pr TE + (1 - Pr TE))).comp Q0s) := by
    simp only [hNh, Nc, key w hw]
  have hNc : ∀ z, N (TF z) = TF (N z) := by
    intro z
    simp only [hN, ContinuousLinearMap.comp_apply]
    rw [hQsc w hw, hGc w hw, hQc w hw]
  have hinvN : ∀ z, Ring.inverse N (N z) = z := fun z =>
    congrArg (fun S : F →L[ℝ] F => S z) (Ring.inverse_mul_cancel N hNw)
  have hNinv : ∀ z, N (Ring.inverse N z) = z := fun z =>
    congrArg (fun S : F →L[ℝ] F => S z) (Ring.mul_inverse_cancel N hNw)
  set z := Ring.inverse N y with hz
  have hzf : TF z = z := by
    have h1 : N (TF z) = N z := by rw [hNc, hNinv, hy]
    calc TF z = Ring.inverse N (N (TF z)) := (hinvN _).symm
      _ = Ring.inverse N (N z) := by rw [h1]
      _ = z := hinvN z
  have h2 : Nh z = y := by
    rw [hNhdef, Nhat_apply_fixed hTE2 Q0 Q0s hQ0sc (hAc w hw) hA hzf, ← hNfix w hw z hzf]
    exact hNinv y
  have : Ring.inverse Nh y = z := by
    rw [← h2]
    exact congrArg (fun S : F →L[ℝ] F => S z) (Ring.inverse_mul_cancel Nh (hNunit' w hw))
  rw [this]

end

end AdalyNcwdhTwo.Bridge