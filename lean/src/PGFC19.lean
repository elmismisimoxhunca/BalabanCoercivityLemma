import PGFC18

/-!
# GFC19 -- repo bridge, part 3: complex conjugation, reality of `P_{ΔW} f` for real `f`, real preimages.
Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

/-- complex conjugation on site fields -/
noncomputable def conjS (φ : TS L) : TS L := WithLp.toLp 2 (fun x => (starRingEnd ℂ) (φ x))

theorem conjS_apply (φ : TS L) (x : Site L) : conjS φ x = (starRingEnd ℂ) (φ x) := rfl

theorem conjS_conjS (φ : TS L) : conjS (conjS φ) = φ := by ext x; simp [conjS_apply]

theorem conjS_add (φ ψ : TS L) : conjS (φ + ψ) = conjS φ + conjS ψ := by ext x; simp [conjS_apply]

theorem conjS_smul_real (r : ℝ) (φ : TS L) : conjS ((r : ℂ) • φ) = (r : ℂ) • conjS φ := by
  ext x; simp [conjS_apply]

theorem inner_conjS (φ ψ : TS L) : ⟪conjS φ, conjS ψ⟫ = (starRingEnd ℂ) ⟪φ, ψ⟫ := by
  simp only [PiLp.inner_apply, conjS_apply, map_sum, map_mul, RCLike.inner_apply, Complex.conj_conj]

theorem conjS_lap (φ : TS L) : conjS (lapC L φ) = lapC L (conjS φ) := by
  ext x
  simp only [conjS_apply, lapC_apply, map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [map_sub, map_mul, map_ofNat, conjS_apply]

theorem conjS_mem_Wc (hdvd : ∀ μ, n ∣ L μ + 1) {φ : TS L} (hφ : φ ∈ Wc (n := n) hdvd) : conjS φ ∈ Wc (n := n) hdvd := by
  intro c hc
  have := hφ c hc
  simp only [conjS_apply]
  rw [← map_sum, this, map_zero]

theorem conjS_mem_DW (hdvd : ∀ μ, n ∣ L μ + 1) {y : TS L} (hy : y ∈ DW (n := n) hdvd) : conjS y ∈ DW (n := n) hdvd := by
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨conjS w, conjS_mem_Wc hdvd hw, (conjS_lap w).symm⟩

theorem Pw_conj (hdvd : ∀ μ, n ∣ L μ + 1) (f : TS L) : Pw hdvd (conjS f) = conjS (Pw hdvd f) := by
  unfold Pw
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact conjS_mem_DW hdvd (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have h0 := Submodule.starProjection_inner_eq_zero f (conjS w) (conjS_mem_DW hdvd hw)
    have : conjS f - conjS ((DW (n := n) hdvd).starProjection f) = conjS (f - (DW (n := n) hdvd).starProjection f) := by
      ext x; simp [conjS_apply]
    rw [this]
    have h2 := inner_conjS (f - (DW (n := n) hdvd).starProjection f) (conjS w)
    rw [conjS_conjS] at h2
    rw [h2, h0, map_zero]

/-- real preimage: if `P f` is real then it is `Δ` of a REAL block-mean-zero field -/
theorem exists_real_preimage (hdvd : ∀ μ, n ∣ L μ + 1) (f : TS L) (hf : conjS f = f) :
    ∃ w : Site L → ℝ, (WithLp.toLp 2 (fun x => ((w x : ℝ) : ℂ)) : TS L) ∈ Wc (n := n) hdvd ∧
      lapC L (WithLp.toLp 2 (fun x => ((w x : ℝ) : ℂ))) = Pw hdvd f := by
  have hP : conjS (Pw hdvd f) = Pw hdvd f := by rw [← Pw_conj, hf]
  have hmem : Pw hdvd f ∈ DW (n := n) hdvd := Submodule.starProjection_apply_mem _ _
  obtain ⟨w0, hw0, hw0l⟩ := hmem
  -- real part
  set w1 : TS L := ((1 / 2 : ℝ) : ℂ) • (w0 + conjS w0) with hw1
  have hw1W : w1 ∈ Wc (n := n) hdvd :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hw0 (conjS_mem_Wc hdvd hw0))
  have hw1real : conjS w1 = w1 := by
    rw [hw1, conjS_smul_real, conjS_add, conjS_conjS, add_comm]
  have hw1fun : (WithLp.toLp 2 (fun x => (((w1 x).re : ℝ) : ℂ)) : TS L) = w1 := by
    ext x
    have h := congrArg (fun F => F x) hw1real
    simp only [conjS_apply] at h
    have him : (w1 x).im = 0 := by
      have := congrArg Complex.im h
      simp at this
      linarith
    simp only
    exact Complex.ext (by simp) (by simp [him])
  refine ⟨fun x => (w1 x).re, ?_, ?_⟩
  · rw [hw1fun]; exact hw1W
  · rw [hw1fun, hw1, map_smul, map_add, hw0l, ← conjS_lap, hw0l, hP]
    ext x
    simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    push_cast
    ring

#print axioms exists_real_preimage

end AdalyFormal.FlatCoercivity
