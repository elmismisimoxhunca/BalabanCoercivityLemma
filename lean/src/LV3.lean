import LV2

/-!
# LV3 -- rows, the gradient row formula, and the row-vs-flux error bounds

* `Rw m A z μ = m⁻⁴ Σ_{u ∈ cube m} Σ_{t<m} A(z + off u + t e_μ, μ)` (= `lineCoarseRestrictSuTwo`, `Rw_lcr`).
* `Phm m φ z = m⁻³ Σ_{u ∈ cube m} φ(z + off u)` (block average); `Rw_grad` : `Rw m (Dφ) z μ = m⁻¹ (Phm(z + m e_μ) - Phm z)`.
* `pair_le` (the workhorse): the lattice sum of `‖avg_A f(z+u+a) - avg_B f(z+u+b)‖²` is `≤ n⁻³ · 36 R² · E1 f` when all
  offset coordinates are `≤ R` (Jensen + tiling + translation estimate).
* `err_small` : `Σ_{z ∈ nℤ³} n ‖Rw n c z μ - Fl n n c z μ‖² ≤ 36 E1(c_μ)`;
  `err_big` : `Σ_{Z ∈ Nℤ³} N ‖Rw N c Z μ - Fl n N c Z μ‖² ≤ 144 ℓ³ E1(c_μ)` (`N = n ℓ`);
  `Fl_shift` : `Σ_{z ∈ nℤ³} ‖Fl n n c (z + off a) μ - Fl n n c (z + off b) μ‖² ≤ n⁻³ · 36 (R+n)² E1(c_μ)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.FlatCoercivity (eU shift_eq pathSite_eq)

variable {L : PeriodicLatticeExtent}

/-- the row value (line average from the block at `z` to the block at `z + m e_μ`). -/
noncomputable def Rw (m : ℕ) (A : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (((m : ℝ) ^ 4)⁻¹) • ∑ u ∈ cube m, ∑ t ∈ Finset.range m, A (z + off L u + t • eU L μ, μ)

/-- block average -/
noncomputable def Phm (m : ℕ) (φ : PeriodicLatticeSite L → SuTwo) (z : PeriodicLatticeSite L) : SuTwo :=
  (((m : ℝ) ^ 3)⁻¹) • ∑ u ∈ cube m, φ (z + off L u)

theorem Rw_lcr (m : ℕ) (A : Bond L → SuTwo) (b : AdalyFormal.Balaban.LatticeOperators.CoarseBond L m)
    (hfit : ∀ μ : Fin 3, ((b.1 : PeriodicLatticeSite L) μ).val + m ≤ L μ + 1) :
    AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo m A b = Rw m A b.1 b.2 := by
  unfold AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo Rw
  rw [block_cube m _ hfit, one_div]
  simp only [pathSite_eq]

theorem Rw_add (m : ℕ) (A B : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    Rw m (A + B) z μ = Rw m A z μ + Rw m B z μ := by
  unfold Rw
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Finset.sum_add_distrib]
  rfl

/-- the gradient row formula. -/
theorem Rw_grad (m : ℕ) (hm : 0 < m) (φ : SiteL2 L) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    Rw m (gradL2 (flatCfg : Cfg L) φ).ofLp z μ
      = (((m : ℝ))⁻¹) • (Phm m φ.ofLp (z + m • eU L μ) - Phm m φ.ofLp z) := by
  have hg : ∀ y : PeriodicLatticeSite L, (gradL2 (flatCfg : Cfg L) φ).ofLp (y, μ) = φ.ofLp (y + eU L μ) - φ.ofLp y := by
    intro y
    have h := AdalyFormal.GenuineU1H.gradL2_flat_apply (L := L) φ (y, μ)
    rw [shift_eq] at h
    exact h
  have htel : ∀ u ∈ cube m, ∑ t ∈ Finset.range m, (gradL2 (flatCfg : Cfg L) φ).ofLp (z + off L u + t • eU L μ, μ)
      = φ.ofLp (z + m • eU L μ + off L u) - φ.ofLp (z + off L u) := by
    intro u _
    simp only [hg]
    have h := Finset.sum_range_sub (fun t => φ.ofLp (z + off L u + t • eU L μ)) m
    simp only [zero_smul, add_zero] at h
    rw [show z + m • eU L μ + off L u = z + off L u + m • eU L μ by abel, ← h]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [succ_nsmul, add_assoc]
  unfold Rw Phm
  rw [Finset.sum_congr rfl htel, Finset.sum_sub_distrib, ← smul_sub, smul_smul]
  congr 1
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

/-! ## the pair lemma -/

theorem l1_le (u : Fin 3 → ℕ) (R : ℕ) (h : ∀ ν, u ν ≤ R) : l1 u ≤ 3 * R := by
  unfold l1; have := h 0; have := h 1; have := h 2; omega

/-- the lattice as a finset -/
noncomputable def latF (L : PeriodicLatticeExtent) (n : ℕ) : Finset (PeriodicLatticeSite L) := by
  classical exact Finset.univ.filter (fun z => OnLatN n z)

theorem mem_latF (n : ℕ) (z : PeriodicLatticeSite L) : z ∈ latF L n ↔ OnLatN n z := by
  classical
  unfold latF; simp

theorem sum_latF {M : Type*} [AddCommMonoid M] (n : ℕ) (g : PeriodicLatticeSite L → M) :
    ∑ z ∈ latF L n, g z = ∑ z : PeriodicLatticeSite L, (if OnLatN n z then g z else 0) := by
  classical
  unfold latF
  rw [Finset.sum_filter]

theorem tiling' {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n) (hdvd : ∀ μ : Fin 3, n ∣ L μ + 1)
    (H : PeriodicLatticeSite L → M) :
    ∑ x, H x = ∑ z ∈ latF L n, ∑ u ∈ cube n, H (z + off L u) := by
  rw [sum_latF, tiling hn hdvd]

theorem fsum4 {A B C D M : Type*} [AddCommMonoid M] (s1 : Finset A) (s2 : Finset B) (s3 : Finset C) (s4 : Finset D)
    (F : A → B → C → D → M) :
    ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, F a b c d = ∑ c ∈ s3, ∑ d ∈ s4, ∑ a ∈ s1, ∑ b ∈ s2, F a b c d := by
  calc ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, F a b c d
      = ∑ a ∈ s1, ∑ c ∈ s3, ∑ b ∈ s2, ∑ d ∈ s4, F a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c ∈ s3, ∑ a ∈ s1, ∑ b ∈ s2, ∑ d ∈ s4, F a b c d := Finset.sum_comm
    _ = ∑ c ∈ s3, ∑ a ∈ s1, ∑ d ∈ s4, ∑ b ∈ s2, F a b c d :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = ∑ c ∈ s3, ∑ d ∈ s4, ∑ a ∈ s1, ∑ b ∈ s2, F a b c d :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

theorem pair_le (f : PeriodicLatticeSite L → SuTwo) {n : ℕ} (hn : 0 < n) (hdvd : ∀ μ : Fin 3, n ∣ L μ + 1)
    {α β : Type*} (A : Finset α) (B : Finset β) (hA : 0 < A.card) (hB : 0 < B.card)
    (a : α → Fin 3 → ℕ) (b : β → Fin 3 → ℕ) (R : ℕ)
    (ha : ∀ x ∈ A, ∀ ν, a x ν ≤ R) (hb : ∀ y ∈ B, ∀ ν, b y ν ≤ R) :
    ∑ z ∈ latF L n,
        ‖((n : ℝ) ^ 3 * A.card)⁻¹ • ∑ u ∈ cube n, ∑ x ∈ A, f (z + off L u + off L (a x))
          - ((n : ℝ) ^ 3 * B.card)⁻¹ • ∑ u ∈ cube n, ∑ y ∈ B, f (z + off L u + off L (b y))‖ ^ 2
      ≤ ((n : ℝ) ^ 3)⁻¹ * (36 * (R : ℝ) ^ 2) * E1 f := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B.card := by exact_mod_cast hB
  set K : ℝ := (n : ℝ) ^ 3 * A.card * B.card with hK
  have hKp : 0 < K := by positivity
  set w : PeriodicLatticeSite L → (Fin 3 → ℕ) → α → β → SuTwo :=
    fun z u x y => f (z + off L u + off L (a x)) - f (z + off L u + off L (b y)) with hw
  -- pointwise rewriting
  have hpt : ∀ z, ((n : ℝ) ^ 3 * A.card)⁻¹ • ∑ u ∈ cube n, ∑ x ∈ A, f (z + off L u + off L (a x))
      - ((n : ℝ) ^ 3 * B.card)⁻¹ • ∑ u ∈ cube n, ∑ y ∈ B, f (z + off L u + off L (b y))
      = K⁻¹ • ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, w z u x y := by
    intro z
    have e1 : ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, w z u x y
        = (B.card : ℝ) • ∑ u ∈ cube n, ∑ x ∈ A, f (z + off L u + off L (a x))
          - (A.card : ℝ) • ∑ u ∈ cube n, ∑ y ∈ B, f (z + off L u + off L (b y)) := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      simp only [hw, Finset.sum_sub_distrib, Finset.sum_const, Finset.smul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun _ _ => ?_) <;> rw [Nat.cast_smul_eq_nsmul ℝ]
    rw [e1, smul_sub, smul_smul, smul_smul]
    congr 2
    · rw [hK]; field_simp
    · rw [hK]; field_simp
  -- Jensen
  have hJ : ∀ z, ‖K⁻¹ • ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2
      ≤ K⁻¹ * ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2 := by
    intro z
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKp)]
    have j1 := norm_sum_sq_le (cube n) (fun u => ∑ x ∈ A, ∑ y ∈ B, w z u x y)
    have j2 : ∀ u, ‖∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2 ≤ A.card * ∑ x ∈ A, ‖∑ y ∈ B, w z u x y‖ ^ 2 :=
      fun u => norm_sum_sq_le A _
    have j3 : ∀ u x, ‖∑ y ∈ B, w z u x y‖ ^ 2 ≤ B.card * ∑ y ∈ B, ‖w z u x y‖ ^ 2 :=
      fun u x => norm_sum_sq_le B _
    rw [card_cube] at j1
    have j23 : ∀ u, ‖∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2
        ≤ (A.card : ℝ) * B.card * ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2 := by
      intro u
      calc ‖∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2 ≤ (A.card : ℝ) * ∑ x ∈ A, ‖∑ y ∈ B, w z u x y‖ ^ 2 := j2 u
        _ ≤ (A.card : ℝ) * ∑ x ∈ A, ((B.card : ℝ) * ∑ y ∈ B, ‖w z u x y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => j3 u x)) (by positivity)
        _ = (A.card : ℝ) * B.card * ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2 := by rw [← Finset.mul_sum]; ring
    have hall : ‖∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2
        ≤ K * ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2 := by
      calc ‖∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2
          ≤ ((n ^ 3 : ℕ) : ℝ) * ∑ u ∈ cube n, ‖∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2 := j1
        _ ≤ ((n ^ 3 : ℕ) : ℝ) * ∑ u ∈ cube n, ((A.card : ℝ) * B.card * ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun u _ => j23 u)) (by positivity)
        _ = K * ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2 := by
            rw [← Finset.mul_sum, hK]; push_cast; ring
    calc K⁻¹ ^ 2 * ‖∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2
        ≤ K⁻¹ ^ 2 * (K * ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hall (by positivity)
      _ = K⁻¹ * ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2 := by field_simp
  -- sum over the lattice
  have hsum : ∑ z ∈ latF L n, ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2
      = ∑ x ∈ A, ∑ y ∈ B, ∑ v : PeriodicLatticeSite L,
          ‖f (v + off L (a x)) - f (v + off L (b y))‖ ^ 2 := by
    rw [fsum4]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [tiling' hn hdvd (fun v => ‖f (v + off L (a x)) - f (v + off L (b y))‖ ^ 2)]
  have htr : ∀ x ∈ A, ∀ y ∈ B, ∑ v : PeriodicLatticeSite L, ‖f (v + off L (a x)) - f (v + off L (b y))‖ ^ 2
      ≤ 36 * (R : ℝ) ^ 2 * E1 f := by
    intro x hx y hy
    refine (trans_le f (a x) (b y)).trans ?_
    have h1 : ((l1 (a x) : ℕ) : ℝ) ≤ 3 * R := by exact_mod_cast l1_le (a x) R (ha x hx)
    have h2 : ((l1 (b y) : ℕ) : ℝ) ≤ 3 * R := by exact_mod_cast l1_le (b y) R (hb y hy)
    have h0a : (0 : ℝ) ≤ ((l1 (a x) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h0b : (0 : ℝ) ≤ ((l1 (b y) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hE := E1_nonneg f
    have hsq : 2 * (((l1 (a x) : ℕ) : ℝ) ^ 2 + ((l1 (b y) : ℕ) : ℝ) ^ 2) ≤ 36 * (R : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq hE
  calc ∑ z ∈ latF L n, ‖((n : ℝ) ^ 3 * A.card)⁻¹ • ∑ u ∈ cube n, ∑ x ∈ A, f (z + off L u + off L (a x))
          - ((n : ℝ) ^ 3 * B.card)⁻¹ • ∑ u ∈ cube n, ∑ y ∈ B, f (z + off L u + off L (b y))‖ ^ 2
      = ∑ z ∈ latF L n, ‖K⁻¹ • ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, w z u x y‖ ^ 2 :=
        Finset.sum_congr rfl (fun z _ => by rw [hpt z])
    _ ≤ ∑ z ∈ latF L n, K⁻¹ * ∑ u ∈ cube n, ∑ x ∈ A, ∑ y ∈ B, ‖w z u x y‖ ^ 2 :=
        Finset.sum_le_sum (fun z _ => hJ z)
    _ = K⁻¹ * ∑ x ∈ A, ∑ y ∈ B, ∑ v : PeriodicLatticeSite L, ‖f (v + off L (a x)) - f (v + off L (b y))‖ ^ 2 := by
        rw [← Finset.mul_sum, hsum]
    _ ≤ K⁻¹ * ∑ x ∈ A, ∑ y ∈ B, 36 * (R : ℝ) ^ 2 * E1 f :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => htr x hx y hy)))
          (by positivity)
    _ = ((n : ℝ) ^ 3)⁻¹ * (36 * (R : ℝ) ^ 2) * E1 f := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hK]; field_simp

#print axioms Rw_lcr
#print axioms Rw_add
#print axioms Rw_grad
#print axioms l1_le
#print axioms mem_latF
#print axioms sum_latF
#print axioms tiling'
#print axioms fsum4
#print axioms pair_le

end AdalyFormal.LemIFlat
