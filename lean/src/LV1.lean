import LF6
import PGFC20

/-!
# LV1 -- torus analysis for the coupling bound `LemV`

* `off L u` : the torus point of a natural offset `u : Fin 3 → ℕ` (via lane FlatCoercivity's `ιz`), additive.
* `E1 f = Σ_ν Σ_x ‖f(x+e_ν) - f x‖²` (gradient energy of a site function).
* `trans_le` : `Σ_x ‖f(x + off a) - f(x + off b)‖² ≤ 2 ((Σa)² + (Σb)²) · E1 f`  (translation estimate).
* `norm_sum_sq_le` : `‖Σ_{i∈s} w i‖² ≤ |s| · Σ ‖w i‖²`.
* `hodge` : for a bond field `c` at flat `U`, `Σ_μ E1 (c(·,μ)) = ‖curl c‖² + ‖D* c‖²` (lattice Hodge identity).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.FlatCoercivity (eU ιz ιz_add ιz_zero ιz_nsmul ιz_ev fmod fmod_val fin_val_nsmul crd crd_add crd_sub
  crd_sum norm_sq_crd crl L1_coord_norm curl_energy coordB gradAdj_flat_apply)

variable {L : PeriodicLatticeExtent}

/-! ## natural offsets -/

/-- the torus point of a natural offset -/
def off (L : PeriodicLatticeExtent) (u : Fin 3 → ℕ) : PeriodicLatticeSite L := ιz L (fun μ => (u μ : ℤ))

theorem off_add (u v : Fin 3 → ℕ) : off L (u + v) = off L u + off L v := by
  unfold off
  rw [← ιz_add]
  congr 1

theorem off_zero : off L 0 = 0 := by
  unfold off
  rw [← ιz_zero]
  congr 1

theorem off_smul (m : ℕ) (u : Fin 3 → ℕ) : off L (m • u) = m • off L u := by
  unfold off
  rw [← ιz_nsmul]
  congr 1

theorem off_val (u : Fin 3 → ℕ) (μ : Fin 3) : ((off L u) μ).val = u μ % (L μ + 1) := by
  have h := fmod_val (L μ + 1) (Nat.succ_pos _) (u μ : ℤ)
  have h2 : ((u μ : ℤ) % ((L μ + 1 : ℕ) : ℤ)) = ((u μ % (L μ + 1) : ℕ) : ℤ) := (Int.natCast_mod (u μ) (L μ + 1)).symm
  rw [h2] at h
  exact_mod_cast h

theorem off_single (μ : Fin 3) (t : ℕ) : off L (Pi.single μ t) = t • eU L μ := by
  have h1 : (Pi.single μ t : Fin 3 → ℕ) = t • (Pi.single μ 1 : Fin 3 → ℕ) := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp
    · simp [h]
  rw [h1, off_smul]
  congr 1
  rw [← ιz_ev]
  unfold off
  congr 1
  funext ν
  by_cases h : ν = μ
  · subst h; simp [AdalyFormal.FlatCoercivity.ev]
  · simp [AdalyFormal.FlatCoercivity.ev, h]

theorem off_eq_sum (u : Fin 3 → ℕ) :
    off L u = u 0 • eU L 0 + u 1 • eU L 1 + u 2 • eU L 2 := by
  have h : u = Pi.single 0 (u 0) + Pi.single 1 (u 1) + Pi.single 2 (u 2) := by
    funext ν
    fin_cases ν <;> simp
  conv_lhs => rw [h]
  rw [off_add, off_add, off_single, off_single, off_single]

/-! ## the translation estimate -/

/-- gradient energy of a site function -/
noncomputable def E1 (f : PeriodicLatticeSite L → SuTwo) : ℝ :=
  ∑ ν : Fin 3, ∑ x : PeriodicLatticeSite L, ‖f (x + eU L ν) - f x‖ ^ 2

theorem E1_nonneg (f : PeriodicLatticeSite L → SuTwo) : 0 ≤ E1 f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- the translation difference as an `L²` vector -/
noncomputable def tv (f : PeriodicLatticeSite L → SuTwo) (d : PeriodicLatticeSite L) : SiteL2 L :=
  WithLp.toLp 2 (fun x => f (x + d) - f x)

theorem tv_norm_sq (f : PeriodicLatticeSite L → SuTwo) (d : PeriodicLatticeSite L) :
    ‖tv f d‖ ^ 2 = ∑ x, ‖f (x + d) - f x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem sum_translate {M : Type*} [AddCommMonoid M] (g : PeriodicLatticeSite L → M) (d : PeriodicLatticeSite L) :
    ∑ x, g (x + d) = ∑ x, g x :=
  Equiv.sum_comp (Equiv.addRight d) g

theorem tv_add (f : PeriodicLatticeSite L → SuTwo) (d d' : PeriodicLatticeSite L) :
    ‖tv f (d + d')‖ ≤ ‖tv f d‖ + ‖tv f d'‖ := by
  set T1 : SiteL2 L := WithLp.toLp 2 (fun x => f (x + d + d') - f (x + d)) with hT1
  have hsplit : tv f (d + d') = T1 + tv f d := by
    ext x
    simp only [tv, hT1, PiLp.add_apply, WithLp.ofLp_toLp]
    rw [add_assoc]; abel
  have hT1n : ‖T1‖ = ‖tv f d'‖ := by
    have h2 : ‖T1‖ ^ 2 = ‖tv f d'‖ ^ 2 := by
      rw [tv_norm_sq, PiLp.norm_sq_eq_of_L2]
      exact sum_translate (fun y => ‖f (y + d') - f y‖ ^ 2) d
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  rw [hsplit]
  calc ‖T1 + tv f d‖ ≤ ‖T1‖ + ‖tv f d‖ := norm_add_le _ _
    _ = ‖tv f d‖ + ‖tv f d'‖ := by rw [hT1n]; ring

theorem tv_nsmul (f : PeriodicLatticeSite L → SuTwo) (d : PeriodicLatticeSite L) (m : ℕ) :
    ‖tv f (m • d)‖ ≤ m * ‖tv f d‖ := by
  induction m with
  | zero =>
      have : tv f ((0 : ℕ) • d) = 0 := by ext x; simp [tv]
      rw [this, norm_zero]; simp
  | succ m ih =>
      rw [succ_nsmul]
      calc ‖tv f (m • d + d)‖ ≤ ‖tv f (m • d)‖ + ‖tv f d‖ := tv_add f _ _
        _ ≤ m * ‖tv f d‖ + ‖tv f d‖ := by linarith
        _ = ((m + 1 : ℕ) : ℝ) * ‖tv f d‖ := by push_cast; ring

theorem tv_off (f : PeriodicLatticeSite L → SuTwo) (u : Fin 3 → ℕ) :
    ‖tv f (off L u)‖ ≤ u 0 * ‖tv f (eU L 0)‖ + u 1 * ‖tv f (eU L 1)‖ + u 2 * ‖tv f (eU L 2)‖ := by
  rw [off_eq_sum]
  calc ‖tv f (u 0 • eU L 0 + u 1 • eU L 1 + u 2 • eU L 2)‖
      ≤ ‖tv f (u 0 • eU L 0 + u 1 • eU L 1)‖ + ‖tv f (u 2 • eU L 2)‖ := tv_add f _ _
    _ ≤ ‖tv f (u 0 • eU L 0)‖ + ‖tv f (u 1 • eU L 1)‖ + ‖tv f (u 2 • eU L 2)‖ := by
        linarith [tv_add f (u 0 • eU L 0) (u 1 • eU L 1)]
    _ ≤ _ := by linarith [tv_nsmul f (eU L 0) (u 0), tv_nsmul f (eU L 1) (u 1), tv_nsmul f (eU L 2) (u 2)]

theorem E1_eq (f : PeriodicLatticeSite L → SuTwo) :
    E1 f = ‖tv f (eU L 0)‖ ^ 2 + ‖tv f (eU L 1)‖ ^ 2 + ‖tv f (eU L 2)‖ ^ 2 := by
  unfold E1
  rw [Fin.sum_univ_three, tv_norm_sq, tv_norm_sq, tv_norm_sq]

/-- `|u|₁` -/
def l1 (u : Fin 3 → ℕ) : ℕ := u 0 + u 1 + u 2

theorem tv_off_sq (f : PeriodicLatticeSite L → SuTwo) (u : Fin 3 → ℕ) :
    ‖tv f (off L u)‖ ^ 2 ≤ ((l1 u : ℕ) : ℝ) ^ 2 * E1 f := by
  have h := tv_off f u
  set t0 := ‖tv f (eU L 0)‖
  set t1 := ‖tv f (eU L 1)‖
  set t2 := ‖tv f (eU L 2)‖
  have hE := E1_eq f
  set T := Real.sqrt (E1 f) with hT
  have hT2 : T ^ 2 = E1 f := Real.sq_sqrt (E1_nonneg f)
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have h0 : t0 ≤ T := Real.le_sqrt_of_sq_le (by rw [hE]; nlinarith [sq_nonneg t1, sq_nonneg t2])
  have h1 : t1 ≤ T := Real.le_sqrt_of_sq_le (by rw [hE]; nlinarith [sq_nonneg t0, sq_nonneg t2])
  have h2 : t2 ≤ T := Real.le_sqrt_of_sq_le (by rw [hE]; nlinarith [sq_nonneg t0, sq_nonneg t1])
  have hu0 : (0 : ℝ) ≤ u 0 := Nat.cast_nonneg _
  have hu1 : (0 : ℝ) ≤ u 1 := Nat.cast_nonneg _
  have hu2 : (0 : ℝ) ≤ u 2 := Nat.cast_nonneg _
  have hle : ‖tv f (off L u)‖ ≤ ((l1 u : ℕ) : ℝ) * T := by
    unfold l1; push_cast
    nlinarith [mul_le_mul_of_nonneg_left h0 hu0, mul_le_mul_of_nonneg_left h1 hu1, mul_le_mul_of_nonneg_left h2 hu2]
  have hn0 : 0 ≤ ‖tv f (off L u)‖ := norm_nonneg _
  calc ‖tv f (off L u)‖ ^ 2 ≤ (((l1 u : ℕ) : ℝ) * T) ^ 2 := pow_le_pow_left₀ hn0 hle 2
    _ = ((l1 u : ℕ) : ℝ) ^ 2 * E1 f := by rw [mul_pow, hT2]

/-- **the translation estimate** -/
theorem trans_le (f : PeriodicLatticeSite L → SuTwo) (a b : Fin 3 → ℕ) :
    ∑ x, ‖f (x + off L a) - f (x + off L b)‖ ^ 2
      ≤ 2 * (((l1 a : ℕ) : ℝ) ^ 2 + ((l1 b : ℕ) : ℝ) ^ 2) * E1 f := by
  have hpt : ∀ x, ‖f (x + off L a) - f (x + off L b)‖ ^ 2
      ≤ 2 * ‖f (x + off L a) - f x‖ ^ 2 + 2 * ‖f (x + off L b) - f x‖ ^ 2 := by
    intro x
    have h1 : f (x + off L a) - f (x + off L b) = (f (x + off L a) - f x) - (f (x + off L b) - f x) := by abel
    rw [h1]
    have h2 := norm_sub_le (f (x + off L a) - f x) (f (x + off L b) - f x)
    have h0 := norm_nonneg ((f (x + off L a) - f x) - (f (x + off L b) - f x))
    have h3 := pow_le_pow_left₀ h0 h2 2
    nlinarith [sq_nonneg (‖f (x + off L a) - f x‖ - ‖f (x + off L b) - f x‖)]
  refine (Finset.sum_le_sum (fun x _ => hpt x)).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← tv_norm_sq, ← tv_norm_sq]
  nlinarith [tv_off_sq f a, tv_off_sq f b]

/-! ## Jensen -/

theorem norm_sum_sq_le {ι E : Type*} [SeminormedAddCommGroup E] (s : Finset ι) (w : ι → E) :
    ‖∑ i ∈ s, w i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖w i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, w i‖ ≤ ∑ i ∈ s, ‖w i‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖w i‖)
  have h0 : 0 ≤ ‖∑ i ∈ s, w i‖ := norm_nonneg _
  calc ‖∑ i ∈ s, w i‖ ^ 2 ≤ (∑ i ∈ s, ‖w i‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

/-! ## the lattice Hodge identity -/

section hodge
variable (a : PeriodicLatticeSite L × Fin 3 → ℝ)

theorem cross_eq (μ ν : Fin 3) :
    ∑ x : PeriodicLatticeSite L, (a (x + eU L μ, ν) - a (x, ν)) * (a (x + eU L ν, μ) - a (x, μ))
      = ∑ x : PeriodicLatticeSite L, (a (x - eU L μ, μ) - a (x, μ)) * (a (x - eU L ν, ν) - a (x, ν)) := by
  have t1 : ∑ x : PeriodicLatticeSite L, a (x + eU L μ, ν) * a (x + eU L ν, μ)
      = ∑ x : PeriodicLatticeSite L, a (x - eU L μ, μ) * a (x - eU L ν, ν) := by
    rw [← sum_translate (fun x => a (x + eU L μ, ν) * a (x + eU L ν, μ)) (-(eU L μ) - eU L ν)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have e1 : x + (-(eU L μ) - eU L ν) + eU L μ = x - eU L ν := by abel
    have e2 : x + (-(eU L μ) - eU L ν) + eU L ν = x - eU L μ := by abel
    simp only [e1, e2]; ring
  have t2 : ∑ x : PeriodicLatticeSite L, a (x + eU L μ, ν) * a (x, μ)
      = ∑ x : PeriodicLatticeSite L, a (x - eU L μ, μ) * a (x, ν) := by
    rw [← sum_translate (fun x => a (x + eU L μ, ν) * a (x, μ)) (-(eU L μ))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have e1 : x + -(eU L μ) + eU L μ = x := by abel
    have e2 : x + -(eU L μ) = x - eU L μ := by abel
    rw [e1, e2]; ring
  have t3 : ∑ x : PeriodicLatticeSite L, a (x, ν) * a (x + eU L ν, μ)
      = ∑ x : PeriodicLatticeSite L, a (x, μ) * a (x - eU L ν, ν) := by
    rw [← sum_translate (fun x => a (x, ν) * a (x + eU L ν, μ)) (-(eU L ν))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have e1 : x + -(eU L ν) + eU L ν = x := by abel
    have e2 : x + -(eU L ν) = x - eU L ν := by abel
    rw [e1, e2]; ring
  have lhs : ∑ x : PeriodicLatticeSite L, (a (x + eU L μ, ν) - a (x, ν)) * (a (x + eU L ν, μ) - a (x, μ))
      = ∑ x : PeriodicLatticeSite L, a (x + eU L μ, ν) * a (x + eU L ν, μ)
        - ∑ x : PeriodicLatticeSite L, a (x + eU L μ, ν) * a (x, μ)
        - ∑ x : PeriodicLatticeSite L, a (x, ν) * a (x + eU L ν, μ)
        + ∑ x : PeriodicLatticeSite L, a (x, ν) * a (x, μ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_); ring
  have rhs : ∑ x : PeriodicLatticeSite L, (a (x - eU L μ, μ) - a (x, μ)) * (a (x - eU L ν, ν) - a (x, ν))
      = ∑ x : PeriodicLatticeSite L, a (x - eU L μ, μ) * a (x - eU L ν, ν)
        - ∑ x : PeriodicLatticeSite L, a (x - eU L μ, μ) * a (x, ν)
        - ∑ x : PeriodicLatticeSite L, a (x, μ) * a (x - eU L ν, ν)
        + ∑ x : PeriodicLatticeSite L, a (x, ν) * a (x, μ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_); ring
  rw [lhs, rhs, t1, t2, t3]

/-- the real Hodge identity -/
theorem hodge_real :
    ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, (a (x + eU L ν, μ) - a (x, μ)) ^ 2
      = ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3, (1 / 2 : ℝ) * (crl a x μ ν) ^ 2
        + ∑ x : PeriodicLatticeSite L, (∑ μ : Fin 3, (a (x - eU L μ, μ) - a (x, μ))) ^ 2 := by
  have hpt : ∀ x : PeriodicLatticeSite L,
      ∑ μ : Fin 3, ∑ ν : Fin 3, (a (x + eU L ν, μ) - a (x, μ)) ^ 2
        = ∑ μ : Fin 3, ∑ ν : Fin 3, (1 / 2 : ℝ) * (crl a x μ ν) ^ 2
          + (∑ μ : Fin 3, (a (x - eU L μ, μ) - a (x, μ))) ^ 2
          + ∑ μ : Fin 3, ∑ ν : Fin 3, ((a (x + eU L μ, ν) - a (x, ν)) * (a (x + eU L ν, μ) - a (x, μ))
              - (a (x - eU L μ, μ) - a (x, μ)) * (a (x - eU L ν, ν) - a (x, ν))) := by
    intro x
    simp only [Fin.sum_univ_three, crl]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hz : ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
      ((a (x + eU L μ, ν) - a (x, ν)) * (a (x + eU L ν, μ) - a (x, μ))
        - (a (x - eU L μ, μ) - a (x, μ)) * (a (x - eU L ν, ν) - a (x, ν))) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun μ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun ν _ => ?_)
    rw [Finset.sum_sub_distrib, cross_eq a μ ν, sub_self]
  rw [hz, add_zero]

end hodge

theorem sum4_comm {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] (F : A → B → C → D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, ∑ a, ∑ b, F a b c d := by
  have h1 : ∀ a b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, F a b c d := fun a b => Finset.sum_comm
  have h2 : ∀ a, ∑ b, ∑ d, ∑ c, F a b c d = ∑ d, ∑ b, ∑ c, F a b c d := fun a => Finset.sum_comm
  have h3 : ∀ d a, ∑ b, ∑ c, F a b c d = ∑ c, ∑ b, F a b c d := fun d a => Finset.sum_comm
  have h4 : ∀ d, ∑ a, ∑ c, ∑ b, F a b c d = ∑ c, ∑ a, ∑ b, F a b c d := fun d => Finset.sum_comm
  simp only [h1, h2]
  rw [Finset.sum_comm]
  simp only [h3, h4]

/-- **the lattice Hodge identity** at flat `U`: the full gradient energy of a bond field is curl² + div². -/
theorem hodge (c : BondFnL2 L) :
    ∑ μ : Fin 3, E1 (fun x => c.ofLp (x, μ))
      = ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : Cfg L) c‖ ^ 2
        + ‖gradAdj (flatCfg : Cfg L) c‖ ^ 2 := by
  -- coordinates
  have hE : ∑ μ : Fin 3, E1 (fun x => c.ofLp (x, μ))
      = ∑ j, ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
          (crd (c.ofLp (x + eU L ν, μ)) j - crd (c.ofLp (x, μ)) j) ^ 2 := by
    unfold E1
    simp only [norm_sq_crd, crd_sub]
    exact sum4_comm _
  have hC : ‖AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2 (flatCfg : Cfg L) c‖ ^ 2
      = ∑ j, ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
          (1 / 2 : ℝ) * (crl (fun p => crd (c.ofLp p) j) x μ ν) ^ 2 := by
    rw [curl_energy]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [L1_coord_norm]
  have hD : ‖gradAdj (flatCfg : Cfg L) c‖ ^ 2
      = ∑ j, ∑ x : PeriodicLatticeSite L,
          (∑ μ : Fin 3, (crd (c.ofLp (x - eU L μ, μ)) j - crd (c.ofLp (x, μ)) j)) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [show ((gradAdj (flatCfg : Cfg L)) c).ofLp x = (gradAdj (flatCfg : Cfg L) c) x from rfl,
      gradAdj_flat_apply, norm_sq_crd]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [crd_sum]
    simp only [crd_sub]
  rw [hE, hC, hD, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact hodge_real (fun p => crd (c.ofLp p) j)

#print axioms off_add
#print axioms off_zero
#print axioms off_smul
#print axioms off_val
#print axioms off_single
#print axioms off_eq_sum
#print axioms E1_nonneg
#print axioms tv_norm_sq
#print axioms sum_translate
#print axioms tv_add
#print axioms tv_nsmul
#print axioms tv_off
#print axioms E1_eq
#print axioms tv_off_sq
#print axioms trans_le
#print axioms norm_sum_sq_le
#print axioms cross_eq
#print axioms hodge_real
#print axioms sum4_comm
#print axioms hodge

end AdalyFormal.LemIFlat
