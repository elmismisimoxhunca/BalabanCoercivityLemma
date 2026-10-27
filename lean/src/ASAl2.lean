import PSiteC7
import ASAl1

/-!
# ASAl2 -- `site_coercive_nested_al`: PSiteC7 `site_coercive_nested` (text copy, one hypothesis changed) with the tower bound on the
ALIGNED bonds only: `hδ : ∀ i<k, AlignedLinkBound (ell^i) (bgTower (fullGeom L ell k) U i) (δ i)` (ASAl1) instead of `frobSupBond (bgTower ..) ≤ δ i`.
The fine-link hypothesis `frobSupBond U ≤ α/ell^k` is unchanged (all fine edges).  The proof is the PSiteC7 proof with `Ns_telescope`
replaced by `Ns_telescope_al` and the nonnegativity of `δ i` read at an aligned bond.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.AsmM0

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)

variable {L : PeriodicLatticeExtent}

/-- **NESTED SITE COERCIVITY (genuine R2 object, full `k`-level tower, whole torus).**
Hypotheses: `ell ≥ 2`, the stride-`ell^k` blocks tile the torus, `frobSupBond U ≤ α/ell^k`, and a bound
`frobSupBond (Ū^i) ≤ δ_i` for the background tower on levels `i < k`, `Σ_{i<k} 6(ell-1)δ_i ≤ E`.
Conclusion (scaled form, `n = ell^k`):
`(1 − 72α² − 4E²)‖f‖² ≤ max(6, 16/(3a)) · n² · ⟨f, Δ'_a(U) f⟩`. -/
theorem site_coercive_nested_al (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1) (U : Cfg L)
    (a : ℝ) (ha : 0 < a) (α E : ℝ) (hU : frobSupBond U ≤ α / (ell : ℝ) ^ k) (δ : ℕ → ℝ)
    (hδ : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (fullGeom L ell k) U i) (δ i))
    (hE : ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * δ i ≤ E) (f : SiteL2 L) :
    (1 - 72 * α ^ 2 - 4 * E ^ 2) * ‖f‖ ^ 2
      ≤ max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 * ⟪f, DelpA (fullGeom L ell k) U a f⟫ := by
  have hell0 : 0 < ell := by omega
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  have hnat : 0 < ell ^ k := pow_pos hell0 k
  have hncast : (((ell ^ k : ℕ)) : ℝ) = n := by rw [hn]; push_cast; rfl
  set g : PeriodicLatticeSite L → SuTwo := WithLp.ofLp f with hg
  set G := fullGeom L ell k with hG
  set Q : PeriodicLatticeSite L → SuTwo := Qcomposite (bgTower G U) ell k g with hQ
  set F : PeriodicLatticeSite L → SuTwo := Qcomposite (fun _ => trivialU L) ell k g with hF
  have hr : Ns 1 g = ‖f‖ := by
    have h := Ns_one g
    rw [← norm_sq_site f] at h
    exact (pow_left_inj₀ (Ns_nonneg 1 g) (norm_nonneg f) two_ne_zero).mp h
  -- telescoping
  have tel := Ns_telescope_al ell hell0 (bgTower G U) δ k (fun j hj μ => (pow_dvd_pow ell hj).trans (hdvd μ)) hδ g k le_rfl
  rw [hr] at tel
  have hEnn : 0 ≤ E := by
    refine le_trans ?_ hE
    refine Finset.sum_nonneg (fun i hi => ?_)
    have hδi : 0 ≤ δ i := (hδ i (Finset.mem_range.mp hi)).nonneg (fun μ => (pow_dvd_pow ell (Finset.mem_range.mp hi).le).trans (hdvd μ))
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    positivity
  have hQF : Ns (ell ^ k) (Q - F) ≤ E * ‖f‖ :=
    le_trans tel (mul_le_mul_of_nonneg_right hE (norm_nonneg f))
  have hFQ : Ns (ell ^ k) F ≤ Ns (ell ^ k) Q + E * ‖f‖ := by
    have h1 : F = Q - (Q - F) := by abel
    calc Ns (ell ^ k) F = Ns (ell ^ k) (Q - (Q - F)) := by rw [← h1]
      _ ≤ Ns (ell ^ k) Q + Ns (ell ^ k) (Q - F) := Ns_sub_le _ _ _
      _ ≤ _ := by linarith
  -- flat Poincare
  have vgb := HConstruction.SectBAstra.vector_graph_bound (L := L) (ell ^ k) hnat hdvd (fun x => f x)
  rw [hncast] at vgb
  have hflat : ∑ y ∈ CoarseLattice L (ell ^ k), ‖(1 / n ^ 3) • ∑ x ∈ blockOf y (ell ^ k), f x‖ ^ 2
      = ∑ y ∈ CoarseLattice L (ell ^ k), ‖F y‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have := Qflat_eq_blockMean ell hell0 g k y hy
    rw [hF, this, hncast]
  rw [hflat, sum_flat_eq, ← norm_sq_site f] at vgb
  have hFsq : n ^ 3 * ∑ y ∈ CoarseLattice L (ell ^ k), ‖F y‖ ^ 2 = Ns (ell ^ k) F ^ 2 := by
    rw [Ns_sq, hncast]
  -- drift of the gradient
  have hD := gradL2_drift U hU f
  have hDtri : ‖gradL2 (trivialU L) f‖ ^ 2 ≤ 2 * ‖gradL2 U f‖ ^ 2 + 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2) := by
    have h1 : ‖gradL2 (trivialU L) f‖ ≤ ‖gradL2 U f‖ + ‖gradL2 U f - gradL2 (trivialU L) f‖ := by
      have := norm_sub_le (gradL2 U f) (gradL2 U f - gradL2 (trivialU L) f)
      simpa using this
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖gradL2 U f‖ - ‖gradL2 U f - gradL2 (trivialU L) f‖)]
  -- mass identity
  have hid := inner_DelpA_full ell k U a f
  have hq : ∑ y ∈ CoarseLattice L (ell ^ k), ‖Q y‖ ^ 2 * n ^ 3 = Ns (ell ^ k) Q ^ 2 := by
    rw [Ns_sq, hncast, ← Finset.sum_mul]; ring
  have hak := ajSeq_ge ell k hell ha
  -- assemble
  have hNF : 0 ≤ Ns (ell ^ k) F := Ns_nonneg _ _
  have hNQ : 0 ≤ Ns (ell ^ k) Q := Ns_nonneg _ _
  have hFsq2 : Ns (ell ^ k) F ^ 2 ≤ 2 * Ns (ell ^ k) Q ^ 2 + 2 * (E ^ 2 * ‖f‖ ^ 2) := by
    have h := pow_le_pow_left₀ hNF hFQ 2
    nlinarith [sq_nonneg (Ns (ell ^ k) Q - E * ‖f‖)]
  have hcancel : n ^ 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2) = 12 * α ^ 2 * ‖f‖ ^ 2 := by
    field_simp
  have h3 : ‖f‖ ^ 2 ≤ 6 * (n ^ 2 * ‖gradL2 U f‖ ^ 2) + 72 * α ^ 2 * ‖f‖ ^ 2
      + 4 * Ns (ell ^ k) Q ^ 2 + 4 * (E ^ 2 * ‖f‖ ^ 2) := by
    have e1 : 3 * (n : ℝ) ^ 2 * ‖gradL2 (trivialU L) f‖ ^ 2
        ≤ 3 * n ^ 2 * (2 * ‖gradL2 U f‖ ^ 2 + 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2)) := by
      gcongr
    have e2 : 3 * (n : ℝ) ^ 2 * (2 * ‖gradL2 U f‖ ^ 2 + 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2))
        = 6 * (n ^ 2 * ‖gradL2 U f‖ ^ 2) + 6 * (n ^ 2 * (12 * (α / n) ^ 2 * ‖f‖ ^ 2)) := by ring
    rw [hcancel] at e2
    nlinarith [vgb, hFsq, hFsq2, e1, e2]
  have hmass : n ^ 2 * ⟪f, DelpA G U a f⟫
      = n ^ 2 * ‖gradL2 U f‖ ^ 2 + ajSeq a ell k * Ns (ell ^ k) Q ^ 2 := by
    have hid' : ⟪f, DelpA G U a f⟫
        = ‖gradL2 U f‖ ^ 2 + ajSeq a ell k * n * ∑ y ∈ CoarseLattice L (ell ^ k), ‖Q y‖ ^ 2 := hid
    have hNsQ : Ns (ell ^ k) Q ^ 2 = n ^ 3 * ∑ y ∈ CoarseLattice L (ell ^ k), ‖Q y‖ ^ 2 := by
      rw [Ns_sq, hncast]
    rw [hid', hNsQ]
    ring
  have hm1 : (6 : ℝ) ≤ max 6 (16 / (3 * a)) := le_max_left _ _
  have hm2 : 16 / (3 * a) ≤ max 6 (16 / (3 * a)) := le_max_right _ _
  have h4 : 4 ≤ max 6 (16 / (3 * a)) * ajSeq a ell k := by
    have : 4 ≤ (16 / (3 * a)) * ((3 / 4 : ℝ) * a) := by
      field_simp; norm_num
    calc (4 : ℝ) ≤ (16 / (3 * a)) * ((3 / 4 : ℝ) * a) := this
      _ ≤ max 6 (16 / (3 * a)) * ajSeq a ell k := by
          apply mul_le_mul hm2 hak (by positivity) (by linarith)
  have hDU : 0 ≤ n ^ 2 * ‖gradL2 U f‖ ^ 2 := by positivity
  have hNQ2 : 0 ≤ Ns (ell ^ k) Q ^ 2 := sq_nonneg _
  rw [mul_assoc, hmass]
  nlinarith [mul_le_mul_of_nonneg_left hm1 hDU, mul_le_mul_of_nonneg_right h4 hNQ2]


#print axioms site_coercive_nested_al

end AdalyFormal.AsmM0
