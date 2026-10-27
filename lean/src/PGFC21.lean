import PGFC20

/-!
# GFC21 -- repo bridge, part 5: `‖R D* A‖² ≥ Σ_j ‖P_{ΔW} D* A^j‖²`.  Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice)

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent}

theorem crd_sub_sum {ι : Type*} (s : Finset ι) (f : ι → SuTwo) (j : JJ) :
    crd (∑ i ∈ s, f i) j = ∑ i ∈ s, crd (f i) j := crd_sum s f j

/-- coordinates of `D* A` are `D*` of the coordinates -/
theorem Dst_coord (A : BondFnL2 L) (j : JJ) (x : Site L) :
    Dst L (coordB (WithLp.ofLp A) j) x
      = ((crd ((gradAdj (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) A) x) j : ℝ) : ℂ) := by
  rw [Dst_apply, gradAdj_flat_apply, crd_sum]
  push_cast
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [crd_sub]
  simp only [coordB_apply]
  push_cast; rfl

theorem conjS_Dst_coord (A : BondFnL2 L) (j : JJ) : conjS (Dst L (coordB (WithLp.ofLp A) j)) = Dst L (coordB (WithLp.ofLp A) j) := by
  ext x
  rw [conjS_apply, Dst_coord]
  simp

/-- re-embedding of coordinate functions into su(2)-valued site fields -/
noncomputable def embS (w : JJ → Site L → ℝ) : SiteL2 L :=
  WithLp.toLp 2 (fun x => eb.repr.symm (WithLp.toLp 2 (fun j => w j x)))

theorem crd_embS (w : JJ → Site L → ℝ) (x : Site L) (j : JJ) : crd (WithLp.ofLp (embS w) x) j = w j x := by
  simp [embS, crd]

theorem norm_sq_site (f : SiteL2 L) : ‖f‖ ^ 2 = ∑ j, ∑ x : Site L, (crd (WithLp.ofLp f x) j) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [norm_sq_crd]
  rw [Finset.sum_comm]

theorem inner_site (f g : SiteL2 L) :
    inner ℝ f g = ∑ j, ∑ x : Site L, crd (WithLp.ofLp f x) j * crd (WithLp.ofLp g x) j := by
  rw [PiLp.inner_apply]
  have h : ∀ x : Site L, inner ℝ (WithLp.ofLp f x) (WithLp.ofLp g x) = ∑ j, crd (WithLp.ofLp f x) j * crd (WithLp.ofLp g x) j := by
    intro x
    rw [← eb.repr.inner_map_map, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [crd, mul_comm]
  simp only [h]
  rw [Finset.sum_comm]


theorem crd_eq_zero (v : SuTwo) (h : ∀ j, crd v j = 0) : v = 0 := by
  apply eb.repr.injective
  ext j
  simpa [crd] using h j

theorem R_lower (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (A : BondFnL2 (scaleUp ell k Lu)) :
    ∑ j, ‖L3 (scaleUp_tiling ell k Lu hell) (coordB (WithLp.ofLp A) j)‖ ^ 2
      ≤ ‖Rproj (geomOf ell k (fullTower ell k Lu)) (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (gradAdj flatCfg A)‖ ^ 2 := by
  have hdvd : ∀ μ, ell ^ k ∣ (scaleUp ell k Lu) μ + 1 := scaleUp_tiling ell k Lu hell
  have hn : 0 < ell ^ k := pow_pos hell k
  set G := geomOf ell k (fullTower ell k Lu) with hG
  set f : SiteL2 (scaleUp ell k Lu) := gradAdj (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) A with hf
  have hex : ∀ j, ∃ w : Site (scaleUp ell k Lu) → ℝ, (WithLp.toLp 2 (fun x => ((w x : ℝ) : ℂ)) : TS (scaleUp ell k Lu)) ∈ Wc (n := ell ^ k) hdvd ∧
      lapC (scaleUp ell k Lu) (WithLp.toLp 2 (fun x => ((w x : ℝ) : ℂ))) = Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)) :=
    fun j => exists_real_preimage hdvd _ (conjS_Dst_coord A j)
  choose w hwW hwP using hex
  set W : SiteL2 (scaleUp ell k Lu) := embS w with hW
  have hWN : W ∈ NQp G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) := by
    refine mem_NQp_of_blocks ell k Lu hell W (fun z hz => ?_)
    apply crd_eq_zero
    intro j
    rw [crd_sum]
    simp only [hW, crd_embS]
    have hc : Coarse (ell ^ k) z := (coarse_iff z).mpr (mem_CoarseLattice.mp hz)
    rw [block_sum_eq hn hdvd (fun x => w j x) z hc]
    have h0 := hwW j z hc
    have : (((∑ t : Cell (ell ^ k), w j (z + ιc hdvd t) : ℝ)) : ℂ) = 0 := by
      push_cast; exact h0
    exact_mod_cast this
  set y : SiteL2 (scaleUp ell k Lu) := lapFull (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) W with hy
  have hyR : y ∈ RImage G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) := by
    refine Submodule.mem_map.mpr ⟨W, hWN, ?_⟩
    show lapDir G flatCfg W = y
    rw [hG, lapDir_flat]
  have hyc : ∀ (j : JJ) (x : Site (scaleUp ell k Lu)), ((crd (WithLp.ofLp y x) j : ℝ) : ℂ) = Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)) x := by
    intro j x
    rw [← hwP j, lapC_apply, hy, lapFull_flat_apply, crd_sum]
    push_cast
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [crd_sub, crd_sub]
    simp only [crd_embS, hW]
    simp only [two_smul, crd_add, crd_embS]
    push_cast; ring
  have hL3 : ∀ j, L3 hdvd (coordB (WithLp.ofLp A) j) = Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)) := fun j => rfl
  have hN1 : ‖y‖ ^ 2 = ∑ j, ‖L3 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
    rw [norm_sq_site]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hL3, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← hyc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hN2 : inner ℝ f y = ∑ j, ‖L3 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 := by
    rw [inner_site]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hP : Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)) ∈ DW (n := ell ^ k) hdvd := Submodule.starProjection_apply_mem _ _
    have h0 := Submodule.starProjection_inner_eq_zero (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)) _ hP
    have h1 : ⟪Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j), Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j))⟫
        = ⟪Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)), Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j))⟫ := by
      have : ⟪Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j) - Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)), Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j))⟫ = 0 := h0
      rw [inner_sub_left, sub_eq_zero] at this
      exact this
    have h2 : ⟪Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j), Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j))⟫
        = ((∑ x : Site (scaleUp ell k Lu), crd (WithLp.ofLp f x) j * crd (WithLp.ofLp y x) j : ℝ) : ℂ) := by
      rw [PiLp.inner_apply]
      push_cast
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← hyc, Dst_coord]
      simp [← hf, mul_comm]
    have h3 : ⟪Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j)), Pw hdvd (Dst (scaleUp ell k Lu) (coordB (WithLp.ofLp A) j))⟫
        = ((‖L3 hdvd (coordB (WithLp.ofLp A) j)‖ ^ 2 : ℝ) : ℂ) := by
      rw [hL3, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h1, h3] at h2
    exact_mod_cast h2.symm
  have hRy : Rproj G (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) y = y :=
    Submodule.starProjection_eq_self_iff.mpr hyR
  have hkey : ‖y‖ ^ 2 = inner ℝ (Rproj G flatCfg f) y := by
    rw [Rproj_symm, hRy, hN2, hN1]
  have hCS : inner ℝ (Rproj G flatCfg f) y ≤ ‖Rproj G flatCfg f‖ * ‖y‖ := real_inner_le_norm _ _
  rw [← hN1]
  by_cases hy0 : ‖y‖ = 0
  · rw [hy0, zero_pow two_ne_zero]; exact sq_nonneg _
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    have : ‖y‖ ≤ ‖Rproj G flatCfg f‖ := by
      by_contra hc
      push_neg at hc
      nlinarith [hkey, hCS]
    nlinarith [this, norm_nonneg y]

#print axioms R_lower

end AdalyFormal.FlatCoercivity
