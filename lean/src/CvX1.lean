import Mathlib

/-!
# CvX1 -- first crossing of a monotone one-parameter family of quadratic forms (lane cover_jacobi_20261016)

`first_crossing`: on a subspace `V` of a finite-dimensional real normed space, let `q c e = a e - (1 - c) * b e` with `a, b` continuous quadratic
forms (`a (r e) = r^2 a e`, same for `b`) and `b >= 0`.  If `q 1` is positive definite on `V` and `q c1 e1 < 0` for some `c1 < 1`, `e1 in V`, then
there is `c* in (c1, 1)` and `e* in V`, `e* != 0`, with `q c* e* = 0`, `q c* >= 0` on all of `V`, and `q c` positive definite on `V` for every `c in (c*, 1]`.
This is the abstract first-crossing (inertia change) step; it is used for the layer weight `c = cos t` in the constrained chain form.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Set Metric

theorem first_crossing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (a b : E → ℝ) (ha : Continuous a) (hb : Continuous b)
    (ha2 : ∀ (r : ℝ) (e : E), a (r • e) = r ^ 2 * a e) (hb2 : ∀ (r : ℝ) (e : E), b (r • e) = r ^ 2 * b e)
    (hbnn : ∀ e, 0 ≤ b e)
    (hpos : ∀ e ∈ V, e ≠ 0 → 0 < a e)
    (c1 : ℝ) (hc1 : c1 < 1) (e1 : E) (he1 : e1 ∈ V) (hneg : a e1 - (1 - c1) * b e1 < 0) :
    ∃ cs : ℝ, c1 < cs ∧ cs < 1 ∧ (∃ es ∈ V, es ≠ 0 ∧ a es - (1 - cs) * b es = 0) ∧
      (∀ e ∈ V, 0 ≤ a e - (1 - cs) * b e) ∧
      (∀ c : ℝ, cs < c → c ≤ 1 → ∀ e ∈ V, e ≠ 0 → 0 < a e - (1 - c) * b e) := by
  classical
  set S : Set E := sphere (0 : E) 1 ∩ (V : Set E) with hS
  have hVclosed : IsClosed (V : Set E) := Submodule.closed_of_finiteDimensional V
  have hScomp : IsCompact S := (isCompact_sphere (0 : E) 1).inter_right hVclosed
  let q : ℝ → E → ℝ := fun c e => a e - (1 - c) * b e
  have hqc : Continuous (fun x : ℝ × E => q x.1 x.2) := by
    have : Continuous (fun x : ℝ × E => a x.2 - (1 - x.1) * b x.2) :=
      (ha.comp continuous_snd).sub ((continuous_const.sub continuous_fst).mul (hb.comp continuous_snd))
    exact this
  let Z : Set ℝ := Prod.fst '' ({x : ℝ × E | x.1 ∈ Icc c1 1 ∧ x.2 ∈ S ∧ q x.1 x.2 ≤ 0})
  have hZcomp : IsCompact Z := by
    have hK : IsCompact ((Icc c1 1) ×ˢ S) := isCompact_Icc.prod hScomp
    have hclosed : IsClosed {x : ℝ × E | x.1 ∈ Icc c1 1 ∧ x.2 ∈ S ∧ q x.1 x.2 ≤ 0} := by
      have h1 : IsClosed {x : ℝ × E | x ∈ (Icc c1 1) ×ˢ S} := hK.isClosed
      have h2 : IsClosed {x : ℝ × E | q x.1 x.2 ≤ 0} := isClosed_le hqc continuous_const
      have := h1.inter h2
      convert this using 1
      ext x; simp [and_assoc]
    have hsub : {x : ℝ × E | x.1 ∈ Icc c1 1 ∧ x.2 ∈ S ∧ q x.1 x.2 ≤ 0} ⊆ (Icc c1 1) ×ˢ S := by
      intro x hx; exact ⟨hx.1, hx.2.1⟩
    exact (hK.of_isClosed_subset hclosed hsub).image continuous_fst
  -- c1 ∈ Z
  have he1ne : e1 ≠ 0 := by
    intro h; rw [h] at hneg; simp [ha2 0 0, hb2 0 0] at hneg
    have h0a : a (0 : E) = 0 := by simpa using ha2 0 0
    have h0b : b (0 : E) = 0 := by simpa using hb2 0 0
    rw [h0a, h0b] at hneg; simp at hneg
  have hn1 : 0 < ‖e1‖ := norm_pos_iff.mpr he1ne
  have hqscale : ∀ (c : ℝ) (r : ℝ) (e : E), q c (r • e) = r ^ 2 * q c e := by
    intro c r e
    show a (r • e) - (1 - c) * b (r • e) = r ^ 2 * (a e - (1 - c) * b e)
    rw [ha2, hb2]; ring
  have hc1Z : c1 ∈ Z := by
    refine ⟨(c1, (‖e1‖⁻¹) • e1), ⟨⟨le_rfl, hc1.le⟩, ⟨?_, V.smul_mem _ he1⟩, ?_⟩, rfl⟩
    · simp [norm_smul, hn1.ne']
    · show q c1 ((‖e1‖⁻¹) • e1) ≤ 0
      rw [hqscale]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
  have hZbdd : BddAbove Z := by
    refine ⟨1, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact hx.1.2
  have hcsZ : sSup Z ∈ Z := hZcomp.sSup_mem ⟨c1, hc1Z⟩
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hxcs⟩ := hcsZ
  have hcs_eq : sSup Z = x.1 := hxcs.symm
  have hxS : ‖x.2‖ = 1 := by simpa using hx2.1
  have hxV : x.2 ∈ V := hx2.2
  have hxne : x.2 ≠ 0 := by
    intro h; rw [h] at hxS; simp at hxS
  -- positivity just above cs
  have hposabove : ∀ c : ℝ, sSup Z < c → c ≤ 1 → ∀ e ∈ V, e ≠ 0 → 0 < q c e := by
    intro c hc hc1' e heV hene
    by_contra hle0
    have hle := not_lt.mp hle0
    have hnorm : 0 < ‖e‖ := norm_pos_iff.mpr hene
    have hcZ : c ∈ Z := by
      refine ⟨(c, (‖e‖⁻¹) • e), ⟨⟨?_, hc1'⟩, ⟨?_, V.smul_mem _ heV⟩, ?_⟩, rfl⟩
      · have : c1 ≤ sSup Z := by
          rw [hcs_eq]; exact hx1.1
        linarith
      · simp [norm_smul, hnorm.ne']
      · show q c ((‖e‖⁻¹) • e) ≤ 0
        rw [hqscale]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
    exact absurd (le_csSup hZbdd hcZ) (not_le.mpr hc)
  have hcs_lt : sSup Z < 1 := by
    rcases lt_or_eq_of_le (show sSup Z ≤ 1 from csSup_le ⟨c1, hc1Z⟩ (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz; exact hy.1.2)) with h | h
    · exact h
    · exfalso
      have h1 : q 1 x.2 ≤ 0 := by
        have e1' : x.1 = 1 := by rw [hxcs, h]
        have := hx3
        rw [e1'] at this
        exact this
      have : 0 < a x.2 := hpos x.2 hxV hxne
      have : q 1 x.2 = a x.2 := by simp [q]
      linarith
  have hpsd : ∀ e ∈ V, 0 ≤ q (sSup Z) e := by
    intro e heV
    by_contra hlt0
    have hlt := not_le.mp hlt0
    have hene : e ≠ 0 := by
      intro h; rw [h] at hlt
      have h0a : a (0 : E) = 0 := by simpa using ha2 0 0
      have h0b : b (0 : E) = 0 := by simpa using hb2 0 0
      simp [q, h0a, h0b] at hlt
    set u : ℝ := -(q (sSup Z) e) with hu
    have hupos : 0 < u := by rw [hu]; linarith
    set B : ℝ := b e with hB
    have hB0 : 0 ≤ B := hbnn e
    set δ : ℝ := min (1 - sSup Z) (u / (B + 1)) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (div_pos hupos (by linarith))
    have hδle : δ ≤ 1 - sSup Z := min_le_left _ _
    have hδle2 : δ ≤ u / (B + 1) := min_le_right _ _
    have hq : q (sSup Z + δ) e = q (sSup Z) e + δ * B := by
      show a e - (1 - (sSup Z + δ)) * b e = (a e - (1 - sSup Z) * b e) + δ * b e
      ring
    have hneg2 : q (sSup Z + δ) e < 0 := by
      rw [hq]
      have : δ * B ≤ u / (B + 1) * B := mul_le_mul_of_nonneg_right hδle2 hB0
      have h3 : u / (B + 1) * B < u := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith
      have : q (sSup Z) e = -u := by rw [hu]; ring
      linarith
    have := hposabove (sSup Z + δ) (by linarith) (by linarith) e heV hene
    linarith
  refine ⟨sSup Z, ?_, hcs_lt, ⟨x.2, hxV, hxne, ?_⟩, hpsd, hposabove⟩
  · have hle : c1 ≤ sSup Z := by rw [hcs_eq]; exact hx1.1
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have := hpsd e1 he1
      rw [← h] at this
      have h' : q c1 e1 = a e1 - (1 - c1) * b e1 := rfl
      linarith
  · have h1 : q (sSup Z) x.2 ≤ 0 := by rw [hcs_eq]; exact hx3
    have h2 := hpsd x.2 hxV
    show a x.2 - (1 - sSup Z) * b x.2 = 0
    have : q (sSup Z) x.2 = a x.2 - (1 - sSup Z) * b x.2 := rfl
    linarith

#print axioms first_crossing

end AdalyFormal.CoverJacobi
