import UA1
import AdalyFormal.Balaban.FourierFaithfulU1

/-!
# UA2 -- IMS algebra at the unit level (lane m2_unit_20261014)

`hmul h X b = h(b.1) • X b` (a site function multiplying a bond field at the bond's base point).
* `flatCurl_hmul` : `flatCurl (h X) p = h(p₀) flatCurl X p + [(h(p₀+μ) − h(p₀)) X(p₀+μ,ν) − (h(p₀+ν) − h(p₀)) X(p₀+ν,μ)]`.
* `q1_hmul`       : `q₁(h X) c = h(c₀) q₁ X c + ℓ⁻⁴ Σ_{x∈B(c₀)} Σ_{j<ℓ} (h(x+jμ) − h(c₀)) X(x+jμ, μ)`.
* `sq_add_young`, `sq_sub_two`, `sq_sum_le_card` : elementary norm inequalities.
* `sum_path_bonds` : `Σ_c Σ_{x∈B(c₀)} Σ_{j<ℓ} f(x+jμ_c, μ_c) = ℓ Σ_b f b` (each bond is read once per offset `j`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.QOne (pathSite)

variable {L : PeriodicLatticeExtent}

/-- a site function multiplying a bond field at the bond's base point. -/
noncomputable def hmul (h : PeriodicLatticeSite L → ℝ) (X : Bond L → SuTwo) : Bond L → SuTwo := fun b => h b.1 • X b

theorem hmul_apply (h : PeriodicLatticeSite L → ℝ) (X : Bond L → SuTwo) (b : Bond L) : hmul h X b = h b.1 • X b := rfl

/-- the curl commutator identity. -/
theorem flatCurl_hmul (h : PeriodicLatticeSite L → ℝ) (X : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    flatCurlValue (hmul h X) p = h p.1 • flatCurlValue X p
      + ((h (periodicLatticeShift p.1 p.2.1.1) - h p.1) • X (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
        - (h (periodicLatticeShift p.1 p.2.1.2) - h p.1) • X (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) := by
  simp only [flatCurlValue, hmul, smul_add, smul_sub, sub_smul]
  abel

/-- the block-average commutator identity. -/
theorem q1_hmul (ell : ℕ) (h : PeriodicLatticeSite L → ℝ) (X : Bond L → SuTwo) (c : CoarseBond L ell) :
    lineCoarseRestrictSuTwo ell (hmul h X) c = h c.1.1 • lineCoarseRestrictSuTwo ell X c
      + (1 / (ell : ℝ) ^ 4) • ∑ x ∈ blockOf c.1.1 ell, ∑ j ∈ Finset.range ell,
          (h (pathSite x c.2 j) - h c.1.1) • X (pathSite x c.2 j, c.2) := by
  simp only [lineCoarseRestrictSuTwo, hmul]
  rw [smul_comm (h c.1.1) (1 / (ell : ℝ) ^ 4), ← smul_add]
  congr 1
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sub_smul]; abel

/-- weighted Young: `‖x + y‖² ≤ (1+ε)‖x‖² + (1+1/ε)‖y‖²`. -/
theorem sq_add_young {E : Type*} [SeminormedAddCommGroup E] (x y : E) {ε : ℝ} (hε : 0 < ε) :
    ‖x + y‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h0 : 0 ≤ ‖x + y‖ := norm_nonneg _
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : 2 * ‖x‖ * ‖y‖ ≤ ε * ‖x‖ ^ 2 + (1 / ε) * ‖y‖ ^ 2 := by
    have hq : 0 ≤ (ε * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
    have e : ε * ‖x‖ ^ 2 + (1 / ε) * ‖y‖ ^ 2 - 2 * ‖x‖ * ‖y‖ = (ε * ‖x‖ - ‖y‖) ^ 2 / ε := by
      field_simp; ring
    have : 0 ≤ (ε * ‖x‖ - ‖y‖) ^ 2 / ε := div_nonneg hq hε.le
    linarith
  nlinarith

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²` (the `ε = 1` case). -/
theorem sq_add_two {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := sq_add_young x y (ε := 1) one_pos
  norm_num at h ⊢
  linarith

/-- `‖a•x − b•y‖² ≤ 2a²‖x‖² + 2b²‖y‖²`. -/
theorem sq_smul_sub_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ) (x y : E) :
    ‖a • x - b • y‖ ^ 2 ≤ 2 * a ^ 2 * ‖x‖ ^ 2 + 2 * b ^ 2 * ‖y‖ ^ 2 := by
  have h := sq_add_two (a • x) (-(b • y))
  rw [← sub_eq_add_neg, norm_neg, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs] at h
  linarith

/-- Cauchy–Schwarz for a finite sum of vectors: `‖Σ_{k∈T} v_k‖² ≤ |T| Σ_{k∈T} ‖v_k‖²`. -/
theorem sq_sum_le_card {ι E : Type*} [SeminormedAddCommGroup E] (T : Finset ι) (v : ι → E) :
    ‖∑ k ∈ T, v k‖ ^ 2 ≤ (T.card : ℝ) * ∑ k ∈ T, ‖v k‖ ^ 2 := by
  have h1 : ‖∑ k ∈ T, v k‖ ≤ ∑ k ∈ T, ‖v k‖ := norm_sum_le T v
  have h0 : 0 ≤ ‖∑ k ∈ T, v k‖ := norm_nonneg _
  have h2 : ‖∑ k ∈ T, v k‖ ^ 2 ≤ (∑ k ∈ T, ‖v k‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (∑ k ∈ T, ‖v k‖) ^ 2 ≤ (T.card : ℝ) * ∑ k ∈ T, ‖v k‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := T) (f := fun k => ‖v k‖)
    simpa using this
  linarith

/-- translation invariance of a site sum along `pathSite`. -/
theorem sum_pathSite (f : PeriodicLatticeSite L → ℝ) (μ : Fin 3) (j : ℕ) :
    ∑ x, f (pathSite x μ j) = ∑ x, f x := by
  have hinj : Function.Injective (fun x : PeriodicLatticeSite L => pathSite x μ j) := by
    have h1 : Function.Injective (fun y : PeriodicLatticeSite L => periodicLatticeShift y μ) :=
      AdalyFormal.Balaban.QOne.periodicLatticeShift_injective μ
    exact h1.iterate j
  have hbij : Function.Bijective (fun x : PeriodicLatticeSite L => pathSite x μ j) :=
    (Finite.injective_iff_bijective).mp hinj
  exact Function.Bijective.sum_comp hbij f

/-- each bond `(z, μ)` is read once for each offset `j < ℓ`: `Σ_c Σ_{x∈B(c₀)} Σ_{j<ℓ} f(x+jμ_c, μ_c) = ℓ Σ_b f b`. -/
theorem sum_path_bonds {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (f : Bond L → ℝ) :
    ∑ c : CoarseBond L ell, ∑ x ∈ blockOf c.1.1 ell, ∑ j ∈ Finset.range ell, f (pathSite x c.2 j, c.2)
      = (ell : ℝ) * ∑ b : Bond L, f b := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hb : ∑ b : Bond L, f b = ∑ μ : Fin 3, ∑ z : PeriodicLatticeSite L, f (z, μ) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hb, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  have h1 : ∑ y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
      ∑ x ∈ blockOf y.1 ell, ∑ j ∈ Finset.range ell, f (pathSite x μ j, μ)
      = ∑ y ∈ CoarseLattice L ell, ∑ x ∈ blockOf y ell, ∑ j ∈ Finset.range ell, f (pathSite x μ j, μ) := by
    have := Finset.sum_coe_sort (CoarseLattice L ell)
      (fun y => ∑ x ∈ blockOf y ell, ∑ j ∈ Finset.range ell, f (pathSite x μ j, μ))
    convert this using 2
    exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  rw [h1, AdalyFormal.Balaban.FourierFaithfulU1.sum_coarse_blocks hell hdvd
    (fun x => ∑ j ∈ Finset.range ell, f (pathSite x μ j, μ))]
  rw [Finset.sum_comm]
  have h2 : ∀ j ∈ Finset.range ell, ∑ x : PeriodicLatticeSite L, f (pathSite x μ j, μ)
      = ∑ z : PeriodicLatticeSite L, f (z, μ) := fun j _ => sum_pathSite (fun z => f (z, μ)) μ j
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.flatCurl_hmul
#print axioms AdalyFormal.M2Unit.q1_hmul
#print axioms AdalyFormal.M2Unit.sq_add_young
#print axioms AdalyFormal.M2Unit.sq_smul_sub_le
#print axioms AdalyFormal.M2Unit.sq_sum_le_card
#print axioms AdalyFormal.M2Unit.sum_path_bonds
