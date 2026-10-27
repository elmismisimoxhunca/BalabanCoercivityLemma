import DLR6

/-!
# DL7 -- row bound of the composite site averaging `Q'_j` (CMP99b (3.19)) and disjointness of the level-`k` blocks

* `boxF y m` : the coordinate box `{x : y_μ ≤ x_μ < y_μ + m}` (no wrap-around, the tree's `blockOf` convention), `card_boxF_le : #box ≤ m³`.
* `Qcomposite_norm_le` : for EVERY background tower, `‖(Q'_j λ)(y)‖ ≤ ℓ^{−3j} Σ_{x ∈ box(y, ℓ^j)} ‖λ x‖` (the transports are isometries,
  `norm_RMap`; the strided sub-boxes of one block are disjoint).
* `Qcomposite_sq_le` : `‖(Q'_j λ)(y)‖² ≤ ℓ^{−3j} Σ_{x ∈ box(y,ℓ^j)} ‖λ x‖²` (Cauchy–Schwarz with `#box ≤ ℓ^{3j}`).
* `boxF_disjoint` : boxes of side `m` based at points with all coordinates divisible by `m` are disjoint unless equal.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.QjComposite (Qcomposite stepAverage stepBlockOf mem_stepBlockOf inStepBlock)

variable {L : PeriodicLatticeExtent}

/-- the coordinate box `[y, y + m)` (no wrap-around) -/
def boxF (y : PeriodicLatticeSite L) (m : ℕ) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (fun x => ∀ μ : Fin 3, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + m)

theorem mem_boxF {y x : PeriodicLatticeSite L} {m : ℕ} :
    x ∈ boxF y m ↔ ∀ μ : Fin 3, (y μ).val ≤ (x μ).val ∧ (x μ).val < (y μ).val + m := by
  simp [boxF]

theorem card_boxF_le (y : PeriodicLatticeSite L) (m : ℕ) : (boxF y m).card ≤ m ^ 3 := by
  classical
  -- injection x ↦ (x_μ − y_μ)_μ into Fin 3 → Fin m
  by_cases hm : m = 0
  · subst hm
    have : boxF y 0 = ∅ := by
      ext x; simp only [mem_boxF, Finset.notMem_empty, iff_false, not_forall]
      exact ⟨0, fun h => by omega⟩
    rw [this]; simp
  have hm' : 0 < m := Nat.pos_of_ne_zero hm
  let g : PeriodicLatticeSite L → (Fin 3 → Fin m) := fun x μ =>
    ⟨((x μ).val - (y μ).val) % m, Nat.mod_lt _ hm'⟩
  have hinj : Set.InjOn g (boxF y m : Set (PeriodicLatticeSite L)) := by
    intro x hx x' hx' hgx
    funext μ
    have h1 := (mem_boxF.mp hx) μ
    have h2 := (mem_boxF.mp hx') μ
    have h3 := congrFun hgx μ
    simp only [g, Fin.mk.injEq] at h3
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    exact Fin.ext (by omega)
  have := Finset.card_le_card_of_injOn g (fun x _ => Finset.mem_univ (g x)) hinj
  simpa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using this

/-- the strided sub-boxes of one block are pairwise disjoint and contained in the block -/
theorem sub_box_subset {y x : PeriodicLatticeSite L} {s ell : ℕ} (hx : x ∈ stepBlockOf y s ell) :
    boxF x s ⊆ boxF y (s * ell) := by
  intro z hz
  rw [mem_boxF] at hz ⊢
  have hx' := (mem_stepBlockOf.mp hx)
  intro μ
  obtain ⟨h1, h2, ⟨d, hd⟩⟩ := hx' μ
  obtain ⟨h3, h4⟩ := hz μ
  refine ⟨le_trans h1 h3, ?_⟩
  -- x_μ − y_μ = s d with s d < s ell, so x_μ + s ≤ y_μ + s ell
  have hlt : s * d < s * ell := by omega
  have hd' : d < ell := by
    by_contra hc; push_neg at hc
    have := Nat.mul_le_mul_left s hc; omega
  have : s * d + s ≤ s * ell := by
    have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hd'); simpa [Nat.mul_succ] using this
  omega

theorem sub_box_disjoint {y x x' : PeriodicLatticeSite L} {s ell : ℕ} (hx : x ∈ stepBlockOf y s ell)
    (hx' : x' ∈ stepBlockOf y s ell) (hne : x ≠ x') : Disjoint (boxF x s) (boxF x' s) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  apply hne
  funext μ
  obtain ⟨a1, a2, ⟨d, hd⟩⟩ := (mem_stepBlockOf.mp hx) μ
  obtain ⟨b1, b2, ⟨e, he⟩⟩ := (mem_stepBlockOf.mp hx') μ
  obtain ⟨c1, c2⟩ := (mem_boxF.mp hz) μ
  obtain ⟨d1, d2⟩ := (mem_boxF.mp hz') μ
  apply Fin.ext
  -- x_μ = y_μ + s d, x'_μ = y_μ + s e, both ≤ z_μ < (·) + s  ⇒  d = e
  have hx_eq : (x μ).val = (y μ).val + s * d := by omega
  have hx'_eq : (x' μ).val = (y μ).val + s * e := by omega
  have hde : d = e := by
    rcases lt_trichotomy d e with h | h | h
    · have : s * d + s ≤ s * e := by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt h); simpa [Nat.mul_succ] using this
      omega
    · exact h
    · have : s * e + s ≤ s * d := by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt h); simpa [Nat.mul_succ] using this
      omega
  rw [hx_eq, hx'_eq, hde]

/-- **row bound of the composite averaging**: `‖(Q'_j λ)(y)‖ ≤ ℓ^{−3j} Σ_{x∈box(y,ℓ^j)} ‖λ x‖`, every tower. -/
theorem Qcomposite_norm_le (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (j : ℕ) (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    ‖Qcomposite bg ell j lam y‖ ≤ ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ := by
  classical
  induction j generalizing y with
  | zero =>
      simp only [pow_zero, one_mul]
      have hy : y ∈ boxF y 1 := by rw [mem_boxF]; intro μ; omega
      exact Finset.single_le_sum (f := fun x => ‖lam x‖) (fun x _ => norm_nonneg _) hy
  | succ j ih =>
      rw [AdalyFormal.Balaban.QjComposite.Qcomposite_succ]
      unfold stepAverage
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : ‖∑ x ∈ stepBlockOf y (ell ^ j) ell,
          RMap (AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy (ell ^ j) (bg j) y
            (AdalyFormal.Balaban.TowerLawCov.coarseGammaPath (ell ^ j) y x)) (Qcomposite bg ell j lam x)‖
          ≤ ∑ x ∈ stepBlockOf y (ell ^ j) ell, ‖Qcomposite bg ell j lam x‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl (fun x _ => ?_)
        exact AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap _ _
      have h2 : ∑ x ∈ stepBlockOf y (ell ^ j) ell, ‖Qcomposite bg ell j lam x‖
          ≤ ∑ x ∈ stepBlockOf y (ell ^ j) ell, ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ z ∈ boxF x (ell ^ j), ‖lam z‖ :=
        Finset.sum_le_sum (fun x _ => ih x)
      have h3 : ∑ x ∈ stepBlockOf y (ell ^ j) ell, ∑ z ∈ boxF x (ell ^ j), ‖lam z‖
          ≤ ∑ z ∈ boxF y (ell ^ (j + 1)), ‖lam z‖ := by
        rw [← Finset.sum_biUnion (fun x hx x' hx' hne => sub_box_disjoint hx hx' hne)]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => norm_nonneg _)
        intro z hz
        obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
        have := sub_box_subset hx hzx
        rwa [← pow_succ] at this
      calc 1 / (ell : ℝ) ^ 3 * ‖_‖ ≤ 1 / (ell : ℝ) ^ 3 * ∑ x ∈ stepBlockOf y (ell ^ j) ell, ‖Qcomposite bg ell j lam x‖ :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / (ell : ℝ) ^ 3 * ∑ x ∈ stepBlockOf y (ell ^ j) ell,
              ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ z ∈ boxF x (ell ^ j), ‖lam z‖ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (1 / (ell : ℝ) ^ 3) ^ (j + 1) * ∑ x ∈ stepBlockOf y (ell ^ j) ell, ∑ z ∈ boxF x (ell ^ j), ‖lam z‖ := by
            rw [← Finset.mul_sum, pow_succ]; ring
        _ ≤ (1 / (ell : ℝ) ^ 3) ^ (j + 1) * ∑ z ∈ boxF y (ell ^ (j + 1)), ‖lam z‖ :=
            mul_le_mul_of_nonneg_left h3 (by positivity)

/-- squared row bound: `‖(Q'_j λ)(y)‖² ≤ ℓ^{−3j} Σ_{box} ‖λ‖²` -/
theorem Qcomposite_sq_le (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ell : ℕ) (hell : 0 < ell) (j : ℕ) (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    ‖Qcomposite bg ell j lam y‖ ^ 2 ≤ ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ ^ 2 := by
  have h1 := Qcomposite_norm_le bg ell j lam y
  have hcs := sq_sum_le_card_mul_sum_sq (s := boxF y (ell ^ j)) (f := fun x => ‖lam x‖)
  have hcard : ((boxF y (ell ^ j)).card : ℝ) ≤ ((ell : ℝ) ^ 3) ^ j := by
    have := card_boxF_le y (ell ^ j)
    have h' : ((boxF y (ell ^ j)).card : ℝ) ≤ ((ell ^ j) ^ 3 : ℕ) := by exact_mod_cast this
    rw [Nat.cast_pow, Nat.cast_pow] at h'
    rw [← pow_mul, mul_comm, pow_mul] at h'
    exact h'
  have hell' : (0 : ℝ) < ell := by exact_mod_cast hell
  have hw : 0 ≤ (1 / (ell : ℝ) ^ 3) ^ j := by positivity
  have hS : 0 ≤ ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ := Finset.sum_nonneg (fun x _ => norm_nonneg _)
  calc ‖Qcomposite bg ell j lam y‖ ^ 2
      ≤ (((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ((1 / (ell : ℝ) ^ 3) ^ j) ^ 2 * (∑ x ∈ boxF y (ell ^ j), ‖lam x‖) ^ 2 := by ring
    _ ≤ ((1 / (ell : ℝ) ^ 3) ^ j) ^ 2 * (((boxF y (ell ^ j)).card : ℝ) * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ ((1 / (ell : ℝ) ^ 3) ^ j) ^ 2 * (((ell : ℝ) ^ 3) ^ j * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard ?_) (by positivity)
        exact Finset.sum_nonneg (fun x _ => sq_nonneg _)
    _ = ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ ^ 2 := by
        have : ((1 / (ell : ℝ) ^ 3) ^ j) * ((ell : ℝ) ^ 3) ^ j = 1 := by
          rw [← mul_pow]; field_simp; simp
        calc ((1 / (ell : ℝ) ^ 3) ^ j) ^ 2 * (((ell : ℝ) ^ 3) ^ j * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ ^ 2)
            = ((1 / (ell : ℝ) ^ 3) ^ j) * (((1 / (ell : ℝ) ^ 3) ^ j) * ((ell : ℝ) ^ 3) ^ j)
                * ∑ x ∈ boxF y (ell ^ j), ‖lam x‖ ^ 2 := by ring
          _ = _ := by rw [this, mul_one]

/-- boxes of side `m` at points with coordinates divisible by `m` are disjoint unless equal -/
theorem boxF_disjoint {y y' : PeriodicLatticeSite L} {m : ℕ} (hy : ∀ μ, m ∣ (y μ).val) (hy' : ∀ μ, m ∣ (y' μ).val)
    (hne : y ≠ y') : Disjoint (boxF y m) (boxF y' m) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  apply hne
  funext μ
  obtain ⟨d, hd⟩ := hy μ
  obtain ⟨e, he⟩ := hy' μ
  obtain ⟨c1, c2⟩ := (mem_boxF.mp hz) μ
  obtain ⟨d1, d2⟩ := (mem_boxF.mp hz') μ
  apply Fin.ext
  have hde : d = e := by
    rcases lt_trichotomy d e with h | h | h
    · have : m * d + m ≤ m * e := by
        have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt h); simpa [Nat.mul_succ] using this
      omega
    · exact h
    · have : m * e + m ≤ m * d := by
        have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt h); simpa [Nat.mul_succ] using this
      omega
  rw [hd, he, hde]

#print axioms boxF
#print axioms card_boxF_le
#print axioms sub_box_subset
#print axioms sub_box_disjoint
#print axioms Qcomposite_norm_le
#print axioms Qcomposite_sq_le
#print axioms boxF_disjoint

end AdalyFormal.DLayer
