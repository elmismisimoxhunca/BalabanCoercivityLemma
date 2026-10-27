import PSiteC3
import AdalyFormal.Balaban.ClassPropagationUbar

/-!
# SC4 -- one-step estimates for the strided transported average `stepAverage s V ell` (CMP99b (3.19) one factor):
contraction in the level-normalised norm, and drift from the flat average controlled by `frobSupBond V`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage stepAverage_trivialU Qcomposite
  Qcomposite_zero Qcomposite_succ stepAverage_add stepAverage_smul)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.ClassPropagationUbar (card_stepBlockOf_le gammaPath_length_le)

variable {L : PeriodicLatticeExtent}

theorem jensen_block (B : Finset (PeriodicLatticeSite L)) {m : ℕ} (hm : 0 < m) (hcard : B.card ≤ m ^ 3)
    (a : PeriodicLatticeSite L → ℝ) :
    ((1 / (m : ℝ) ^ 3) * ∑ x ∈ B, a x) ^ 2 ≤ (1 / (m : ℝ) ^ 3) * ∑ x ∈ B, a x ^ 2 := by
  have hs := sq_sum_le_card_mul_sum_sq (s := B) (f := a)
  have hmR : (0 : ℝ) < (m : ℝ) ^ 3 := by positivity
  have hc : (B.card : ℝ) ≤ (m : ℝ) ^ 3 := by exact_mod_cast hcard
  have hnn : 0 ≤ ∑ x ∈ B, a x ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  calc ((1 / (m : ℝ) ^ 3) * ∑ x ∈ B, a x) ^ 2 = (1 / (m : ℝ) ^ 3) ^ 2 * (∑ x ∈ B, a x) ^ 2 := by ring
    _ ≤ (1 / (m : ℝ) ^ 3) ^ 2 * ((B.card : ℝ) * ∑ x ∈ B, a x ^ 2) := by gcongr
    _ ≤ (1 / (m : ℝ) ^ 3) ^ 2 * (((m : ℝ) ^ 3) * ∑ x ∈ B, a x ^ 2) := by gcongr
    _ = (1 / (m : ℝ) ^ 3) * ∑ x ∈ B, a x ^ 2 := by field_simp

/-- pointwise contraction of the transported average -/
theorem stepAverage_sq_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (g : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    ‖stepAverage s V ell g y‖ ^ 2 ≤ (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2 := by
  have hcard := card_stepBlockOf_le y (ell := ell) hs
  have h1 : ‖stepAverage s V ell g y‖ ≤ (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ := by
    unfold stepAverage
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap _ _
  have h2 := jensen_block (stepBlockOf y s ell) hell hcard (fun x => ‖g x‖)
  calc ‖stepAverage s V ell g y‖ ^ 2 ≤ ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- pointwise drift: `‖(S(V) − S(1)) g (y)‖² ≤ ε² ℓ⁻³ Σ ‖g‖²` where `ε = 6(ℓ-1) δ`, `δ ≥ frobSupBond V`. -/
theorem stepAverage_drift_sq (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ : frobSupBond V ≤ δ)
    (g : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    ‖stepAverage s V ell g y - stepAverage s (trivialU L) ell g y‖ ^ 2
      ≤ (6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) := by
  have hcard := card_stepBlockOf_le y (ell := ell) hs
  have hδ0 : 0 ≤ δ := le_trans (by
    unfold frobSupBond
    exact (Finset.le_sup'_iff _).mpr ⟨(y, 0), Finset.mem_univ _, AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _⟩) hδ
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ := by
    have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
    positivity
  set ε : ℝ := 6 * ((ell : ℝ) - 1) * δ with hε
  have hpt : ∀ x ∈ stepBlockOf y s ell,
      ‖RMap (coarsePathHolonomy s V y (coarseGammaPath s y x)) (g x) - g x‖ ≤ ε * ‖g x‖ := by
    intro x hx
    have h1 := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le
      (coarsePathHolonomy s V y (coarseGammaPath s y x)) (g x)
    have h2 := AdalyFormal.Balaban.BlockedBackground.frobNorm_coarsePathHolonomy_sub_one_le s V y
      (coarseGammaPath s y x)
    have h3 := AdalyFormal.Balaban.ClassPropagationUbar.gammaPath_length_le y x hs hx
    have h3' : ((coarseGammaPath s y x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
      have : ((coarseGammaPath s y x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by exact_mod_cast h3
      rw [Nat.cast_mul, Nat.cast_sub hell] at this
      simpa using this
    have hlen0 : (0 : ℝ) ≤ ((coarseGammaPath s y x).length : ℝ) := by positivity
    have h4 : AdalyFormal.Balaban.RMapLipschitz.frobNorm
        (((coarsePathHolonomy s V y (coarseGammaPath s y x) : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 3 * ((ell : ℝ) - 1) * δ := by
      calc _ ≤ ((coarseGammaPath s y x).length : ℝ) * frobSupBond V := h2
        _ ≤ ((coarseGammaPath s y x).length : ℝ) * δ := mul_le_mul_of_nonneg_left hδ hlen0
        _ ≤ 3 * ((ell : ℝ) - 1) * δ := mul_le_mul_of_nonneg_right h3' hδ0
    calc _ ≤ 2 * _ * ‖g x‖ := h1
      _ ≤ 2 * (3 * ((ell : ℝ) - 1) * δ) * ‖g x‖ := by gcongr
      _ = ε * ‖g x‖ := by rw [hε]; ring
  have hdiff : stepAverage s V ell g y - stepAverage s (trivialU L) ell g y
      = (1 / (ell : ℝ) ^ 3) • ∑ x ∈ stepBlockOf y s ell,
          (RMap (coarsePathHolonomy s V y (coarseGammaPath s y x)) (g x) - g x) := by
    rw [stepAverage_trivialU, Finset.sum_sub_distrib, smul_sub]
    rfl
  have h1 : ‖stepAverage s V ell g y - stepAverage s (trivialU L) ell g y‖
      ≤ (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ε * ‖g x‖ := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hpt)
  have h2 := jensen_block (stepBlockOf y s ell) hell hcard (fun x => ε * ‖g x‖)
  calc _ ≤ ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ε * ‖g x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, (ε * ‖g x‖) ^ 2 := h2
    _ = ε ^ 2 * ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) := by
        simp_rw [mul_pow, ← Finset.mul_sum]; ring


theorem stepBlock_disjoint {y y' : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hy : y ∈ CoarseLattice L (s * ell)) (hy' : y' ∈ CoarseLattice L (s * ell)) (hne : y ≠ y') :
    Disjoint (stepBlockOf y s ell) (stepBlockOf y' s ell) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  apply hne
  rw [mem_CoarseLattice] at hy hy'
  funext μ
  have h1 := mem_stepBlockOf.mp hx μ
  have h2 := mem_stepBlockOf.mp hx' μ
  obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero (hy μ)
  obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero (hy' μ)
  have hsl : 0 < s * ell := Nat.mul_pos hs hell
  have hab : a = b := by
    refine nat_unique (s := s * ell) (d := (x μ).val) hsl ?_ ?_ ?_ ?_ <;> omega
  subst hab
  apply Fin.ext
  omega

theorem sum_stepBlock_le {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) (F : PeriodicLatticeSite L → ℝ)
    (hF : ∀ x, 0 ≤ F x) :
    ∑ y ∈ CoarseLattice L (s * ell), ∑ x ∈ stepBlockOf y s ell, F x ≤ ∑ x ∈ CoarseLattice L s, F x := by
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hF x)
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact stepBlock_mem_coarse hy hxy
  · intro y hy y' hy' hne
    exact stepBlock_disjoint hs hell hy hy' hne

end AdalyFormal.SiteCoercivity
