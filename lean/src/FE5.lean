import FE4
import AdalyFormal.Balaban.ClassPropagationUbar

/-!
# FE5 -- the flat norm of the top-level constraint map, and `‖Q'_k(U)‖ ≤ q` from the Q'-drift

* `Qtop_flat_norm_sq`: `‖Q'_k(1) f|_{Λ_k}‖² · n³ ≤ ‖f‖²` (`n = ell^k`; Cauchy-Schwarz on each block, corner blocks disjoint).
* `hQq_of_flat`: `‖Qtop U f‖ ≤ (√(1/n³) + ε0) ‖f‖` from the drift hypothesis `hQdrift` alone.
* `ginv_coercive_FE_named2`: FE4's `ginv_coercive_FE_named` with `hQq` discharged (`q = √(1/n³) + ε0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.FlatExt

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF PhiF)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf inBlock Bond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf_one)
open AdalyFormal.Balaban.ClassPropagationUbar (card_stepBlockOf_le)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.StatementLane (scaleUp)

theorem corner_blocks_disjoint (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (y1 y2 : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) (hne : y1 ≠ y2) :
    Disjoint (blockOf y1.1 (ell ^ k)) (blockOf y2.1 (ell ^ k)) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  apply hne
  apply Subtype.ext
  funext μ
  apply Fin.ext
  rw [mem_blockOf] at h1 h2
  obtain ⟨a, ha⟩ := dvd_of_lam ell k Lu y1 μ
  obtain ⟨b, hb⟩ := dvd_of_lam ell k Lu y2 μ
  have g1 := h1 μ
  have g2 := h2 μ
  have e1 : ell ^ k * a < ell ^ k * (b + 1) := by rw [Nat.mul_succ]; omega
  have e2 : ell ^ k * b < ell ^ k * (a + 1) := by rw [Nat.mul_succ]; omega
  have f1 := Nat.lt_of_mul_lt_mul_left e1
  have f2 := Nat.lt_of_mul_lt_mul_left e2
  have hab : a = b := by omega
  rw [ha, hb, hab]

theorem block_card_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (y : PeriodicLatticeSite (scaleUp ell k Lu)) :
    ((blockOf y (ell ^ k)).card : ℝ) ≤ ((ell : ℝ) ^ k) ^ 3 := by
  have := card_stepBlockOf_le y (s := 1) (ell := ell ^ k) one_pos
  rw [stepBlockOf_one] at this
  exact_mod_cast this

theorem norm_sum_sq_le_card {ι V : Type*} [SeminormedAddCommGroup V] (S : Finset ι) (f : ι → V) :
    ‖∑ x ∈ S, f x‖ ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by
  have h1 : ‖∑ x ∈ S, f x‖ ≤ ∑ x ∈ S, ‖f x‖ := norm_sum_le _ _
  have h2 : (∑ x ∈ S, ‖f x‖) ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem corner_sum_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (g : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, ∑ x ∈ blockOf y.1 (ell ^ k), g x ≤ ∑ x, g x := by
  classical
  have hdisj : (↑(Finset.univ : Finset {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) :
      Set {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}).PairwiseDisjoint
        (fun y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k} => blockOf y.1 (ell ^ k)) :=
    fun y1 _ y2 _ hne => corner_blocks_disjoint ell k Lu hell y1 y2 hne
  rw [← Finset.sum_biUnion hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hg x)

theorem c_sq_mul (ell k : ℕ) (hell : 0 < ell) : ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 6 = 1 := by
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hn : ((ell : ℝ) ^ k) ^ 3 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hne)
  have h1 : (1 / (ell : ℝ) ^ 3) ^ k = (((ell : ℝ) ^ k) ^ 3)⁻¹ := by
    rw [one_div, inv_pow]; congr 1; ring
  rw [h1, show ((ell : ℝ) ^ k) ^ 6 = (((ell : ℝ) ^ k) ^ 3) ^ 2 by ring, ← mul_pow, inv_mul_cancel₀ hn, one_pow]

theorem Qtop_flat_norm_point (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (f : SiteL2 (scaleUp ell k Lu)) (y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) :
    ‖Qtop (GF ell k Lu) (trivialU _) f y‖ ^ 2
      ≤ ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 3 * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2 := by
  have hc0 : (0 : ℝ) ≤ (1 / (ell : ℝ) ^ 3) ^ k := by positivity
  rw [Qtop_flat ell k Lu hell f y, norm_smul, Real.norm_of_nonneg hc0]
  have h3 : 0 ≤ ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 := (norm_sum_sq_le_card (blockOf y.1 (ell ^ k)) (fun x => f x)).trans
    (mul_le_mul_of_nonneg_right (block_card_le ell k Lu y.1) h3)
  rw [mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left h4 (sq_nonneg _)

theorem Qtop_flat_norm_sq (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (f : SiteL2 (scaleUp ell k Lu)) :
    ‖Qtop (GF ell k Lu) (trivialU _) f‖ ^ 2 * ((ell : ℝ) ^ k) ^ 3 ≤ ‖f‖ ^ 2 := by
  have hpos3 : (0 : ℝ) ≤ ((ell : ℝ) ^ k) ^ 3 := by positivity
  have hpos6 : (0 : ℝ) ≤ ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 6 := by positivity
  have hsum := corner_sum_le ell k Lu hell (fun x => ‖f x‖ ^ 2) (fun x => sq_nonneg _)
  have hQ : ‖Qtop (GF ell k Lu) (trivialU _) f‖ ^ 2
      = ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, ‖Qtop (GF ell k Lu) (trivialU _) f y‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  have hf : ‖f‖ ^ 2 = ∑ x, ‖f x‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  rw [hQ, hf]
  calc (∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, ‖Qtop (GF ell k Lu) (trivialU _) f y‖ ^ 2)
        * ((ell : ℝ) ^ k) ^ 3
      ≤ (∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k},
          ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 3 * ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2)
          * ((ell : ℝ) ^ k) ^ 3 :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun y _ => Qtop_flat_norm_point ell k Lu hell f y) hpos3
    _ = ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 6 *
          ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, ∑ x ∈ blockOf y.1 (ell ^ k), ‖f x‖ ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((1 / (ell : ℝ) ^ 3) ^ k) ^ 2 * ((ell : ℝ) ^ k) ^ 6 * ∑ x, ‖f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hpos6
    _ = ∑ x, ‖f x‖ ^ 2 := by rw [c_sq_mul ell k hell, one_mul]

theorem Qtop_flat_norm_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (f : SiteL2 (scaleUp ell k Lu)) :
    ‖Qtop (GF ell k Lu) (trivialU _) f‖ ≤ Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) * ‖f‖ := by
  have hn3 : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 3 := pow_pos (pow_pos (by exact_mod_cast hell) k) 3
  refine norm_le_of_sq _ (by positivity) (norm_nonneg _) (norm_nonneg _) ?_
  have h := Qtop_flat_norm_sq ell k Lu hell f
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hn3]
  exact h

theorem hQq_of_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (ε0 : ℝ)
    (hQdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (f : SiteL2 (scaleUp ell k Lu)) :
    ‖Qtop (GF ell k Lu) U f‖ ≤ (Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) + ε0) * ‖f‖ := by
  have h2 := hQdrift f
  have h3 := Qtop_flat_norm_le ell k Lu hell f
  calc ‖Qtop (GF ell k Lu) U f‖ ≤ ‖Qtop (GF ell k Lu) (trivialU _) f‖
        + ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ := by
        have := norm_add_le (Qtop (GF ell k Lu) (trivialU _) f)
          (Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f)
        simpa using this
    _ ≤ _ := by nlinarith

theorem ginv_coercive_FE_named2 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu))
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (PU : ℝ) (hPU : 0 ≤ PU)
    (hPoincU : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (nsq c1 t θ δm e P δ q ε0 : ℝ) (hn : 0 < nsq) (ht : 0 < t) (hP : 0 ≤ P)
    (hδdef : δ = Real.sqrt 12 * frobSupBond U)
    (hedef : e = (1 + t) * θ + (1 + 1 / t) * ((4 * Real.sqrt 2 * frobSupBond U) ^ 2 + δm ^ 2))
    (hqdef : q = Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) + ε0) (hε0 : 0 ≤ ε0) (hεa : ε0 * aFE ell k < 1)
    (hsmall : nsq * ((((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * ε0)) + δ) ^ 2 + nsq * e < c1)
    (hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2))
    (hdp : ∀ x : BondFnL2 (scaleUp ell k Lu),
      |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x| ≤ θ * ‖x‖ ^ 2)
    (hm : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ δm ^ 2 * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖)
    (hQdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * ε0)) + δ) ^ 2
        - nsq * e) / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ := by
  have hq : 0 ≤ q := by rw [hqdef]; positivity
  have hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖ := fun f => by
    rw [hqdef]; exact hQq_of_flat ell k Lu hell U ε0 hQdrift f
  exact ginv_coercive_FE_named ell k Lu hell U a ha Lam hreg hu PU hPU hPoincU nsq c1 t θ δm e P δ q ε0 hn ht hP
    hδdef hedef hq hε0 hεa hsmall hflat hdp hm hPoinc1 hQdrift hQq x

#print axioms corner_blocks_disjoint
#print axioms block_card_le
#print axioms corner_sum_le
#print axioms c_sq_mul
#print axioms Qtop_flat_norm_point
#print axioms Qtop_flat_norm_sq
#print axioms Qtop_flat_norm_le
#print axioms hQq_of_flat
#print axioms ginv_coercive_FE_named2

end AdalyFormal.FlatExt
