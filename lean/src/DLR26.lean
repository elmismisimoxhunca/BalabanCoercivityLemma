import DLR25

/-!
# DL26 -- `Δ'` (the curvature part of `Δ`, CMP99b (3.10)) as an operator: decomposition, size, and Combes–Thomas commutator

On the full tower (`Ω₀` = torus, `plaqIn Ω₀` = all plaquettes):
* `Delta_decomp` : `Δ = C*C + Δ'` as continuous linear maps, `C = curlC U`, `Δ' = DpOp U := deltaPrimeOpLoc U univ`.
* `bilPlaq_quad_le` : `|bilPlaq U p A A| ≤ 136 α₀ ‖A‖²_{∂p}` under `PlaqDef α₀ U` (from the tree per-term bounds re-proved in NF4);
* `Sp` (the per-plaquette symmetrised form, `⟪x,Δ'y⟫ = Σ_p Sp`), `Sp_amgm`, `Sp_bil_le` : `|Sp(A,B)| ≤ 68 α₀ ‖A‖_{∂p} ‖B‖_{∂p}`;
* **`DpOp_norm`** : `‖Δ'‖ ≤ 816 α₀`;  **`DpOp_cjp_norm`/`DpOp_cjm_norm`** : `‖Δ'^± − Δ'‖ ≤ 816 α₀ (e^{2θ'} − 1)`.
  (Weighted form: `(ωx)(b) = e^{φ(p₀)} x'_p(b)` with `x'_p(b) = e^{φ(b₀)−φ(p₀)} x(b)`, so `Sp(ωx, ω⁻¹y) = Sp(x'_p, y'_p)`; on `∂p`
  the bond base points are within one step of `p₀`.)
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.DeltaPrimeOperator (bilPlaq bilPlaq_diag)
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq plaqBondSq_nonneg)

variable {L : PeriodicLatticeExtent}

/-! ## the per-plaquette quadratic bound -/

theorem curl_sq_le_pbs (U : Cfg L) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖curlValueCovariant U A p‖ ^ 2 ≤ 4 * plaqBondSq A p := by
  unfold curlValueCovariant plaqBondSq
  set a := ‖A (p.1, p.2.1.1)‖
  set b := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖
  set c := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖
  set d := ‖A (p.1, p.2.1.2)‖
  have h : ‖A (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
      - RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - A (p.1, p.2.1.2)‖ ≤ a + b + c + d := by
    have h1 := norm_sub_le (A (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
      - RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))) (A (p.1, p.2.1.2))
    have h2 := norm_sub_le (A (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)))
      (RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)))
    have h3 := norm_add_le (A (p.1, p.2.1.1)) (RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)))
    rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap] at h2 h3
    linarith
  have h0 : 0 ≤ ‖A (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
      - RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - A (p.1, p.2.1.2)‖ := norm_nonneg _
  have ha := norm_nonneg (A (p.1, p.2.1.1))
  have hb := norm_nonneg (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
  have hc := norm_nonneg (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
  have hd := norm_nonneg (A (p.1, p.2.1.2))
  have h2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (c - d)]

theorem bilPlaq_quad_le (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |bilPlaq U p A A| ≤ 136 * α₀ * plaqBondSq A p := by
  rw [bilPlaq_diag, AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTermTransported_eq_neg,
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTermTransported_eq_neg]
  have h1 := AdalyFormal.NonflatHunit.abs_deltaPrimeFirstTerm_le' hα₀ U hpl A p
  have h2 := AdalyFormal.NonflatHunit.abs_deltaPrimeSecondTerm_le' hα₀ U hpl A p
  have h3 := curl_sq_le_pbs U A p
  have h4 : 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 ≤ 16 * α₀ * (4 * plaqBondSq A p) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e : -AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTerm U A p
      + -AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTerm U A p
      = -(AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTerm U A p
        + AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTerm U A p) := by ring
  rw [e, abs_neg]
  refine (abs_add_le _ _).trans ?_
  linarith

/-! ## the symmetrised per-plaquette form and its bilinear bound -/

/-- `Sp U p A B = ¼(bilPlaq(A,B) + bilPlaq(B,A))` -/
noncomputable def Sp (U : Cfg L) (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) : ℝ :=
  (1 / 4) * (bilPlaq U p A B + bilPlaq U p B A)

theorem Sp_add_left (U : Cfg L) (p : PeriodicLatticePlaquette L) (A A' B : Bond L → SuTwo) :
    Sp U p (A + A') B = Sp U p A B + Sp U p A' B := by
  unfold Sp; simp only [map_add, LinearMap.add_apply]; ring

theorem Sp_add_right (U : Cfg L) (p : PeriodicLatticePlaquette L) (A B B' : Bond L → SuTwo) :
    Sp U p A (B + B') = Sp U p A B + Sp U p A B' := by
  unfold Sp; simp only [map_add, LinearMap.add_apply]; ring

theorem Sp_smul_left (U : Cfg L) (p : PeriodicLatticePlaquette L) (c : ℝ) (A B : Bond L → SuTwo) :
    Sp U p (c • A) B = c * Sp U p A B := by
  unfold Sp; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem Sp_smul_right (U : Cfg L) (p : PeriodicLatticePlaquette L) (c : ℝ) (A B : Bond L → SuTwo) :
    Sp U p A (c • B) = c * Sp U p A B := by
  unfold Sp; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem Sp_sub_left (U : Cfg L) (p : PeriodicLatticePlaquette L) (A A' B : Bond L → SuTwo) :
    Sp U p (A - A') B = Sp U p A B - Sp U p A' B := by
  unfold Sp; simp only [map_sub, LinearMap.sub_apply]; ring

theorem Sp_sub_right (U : Cfg L) (p : PeriodicLatticePlaquette L) (A B B' : Bond L → SuTwo) :
    Sp U p A (B - B') = Sp U p A B - Sp U p A B' := by
  unfold Sp; simp only [map_sub, LinearMap.sub_apply]; ring

theorem Sp_symm (U : Cfg L) (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Sp U p A B = Sp U p B A := by unfold Sp; ring

theorem pbs_par (A B : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) (s : ℝ) :
    plaqBondSq (s • A + B) p + plaqBondSq (s • A - B) p = 2 * s ^ 2 * plaqBondSq A p + 2 * plaqBondSq B p := by
  unfold plaqBondSq
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  have hp : ∀ u v : SuTwo, ‖s • u + v‖ ^ 2 + ‖s • u - v‖ ^ 2 = 2 * s ^ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    intro u v
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm u v]
    ring
  rw [show ∀ a b c d e f g h : ℝ, (a + b + c + d) + (e + f + g + h) = (a + e) + (b + f) + (c + g) + (d + h) by
    intros; ring]
  rw [hp, hp, hp, hp]; ring

theorem Sp_amgm (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (A B : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) (s : ℝ) (hs : 0 < s) :
    |Sp U p A B| ≤ (68 * α₀ / 2) * (s * plaqBondSq A p + plaqBondSq B p / s) := by
  have key : 4 * s * Sp U p A B = Sp U p (s • A + B) (s • A + B) - Sp U p (s • A - B) (s • A - B) := by
    simp only [Sp_add_left, Sp_add_right, Sp_sub_left, Sp_sub_right, Sp_smul_left, Sp_smul_right, Sp_symm U p B A]
    ring
  have hq : ∀ X : Bond L → SuTwo, |Sp U p X X| ≤ 68 * α₀ * plaqBondSq X p := by
    intro X
    have h := bilPlaq_quad_le U hα₀ hpl X p
    unfold Sp
    rw [show (1 / 4 : ℝ) * (bilPlaq U p X X + bilPlaq U p X X) = (1 / 2) * bilPlaq U p X X by ring, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have h1 := hq (s • A + B)
  have h2 := hq (s • A - B)
  have hpar := pbs_par A B p s
  have h3 : |4 * s * Sp U p A B| ≤ 68 * α₀ * (2 * s ^ 2 * plaqBondSq A p + 2 * plaqBondSq B p) := by
    rw [key, ← hpar, mul_add]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * s)] at h3
  rw [show (68 * α₀ / 2) * (s * plaqBondSq A p + plaqBondSq B p / s)
      = (68 * α₀ * (2 * s ^ 2 * plaqBondSq A p + 2 * plaqBondSq B p)) / (4 * s) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem amgm_to_prod (S β a b : ℝ) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ s : ℝ, 0 < s → |S| ≤ (β / 2) * (s * a + b / s)) : |S| ≤ β * Real.sqrt a * Real.sqrt b := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · -- a = 0
    rw [← ha0, Real.sqrt_zero, mul_zero, zero_mul]
    by_contra hS
    push Not at hS
    rcases eq_or_lt_of_le (mul_nonneg hβ hb) with hbb | hbb
    · have := h 1 one_pos
      rw [← ha0] at this
      have e : (β / 2) * (1 * 0 + b / 1) = (β * b) / 2 := by ring
      rw [e, ← hbb] at this
      linarith
    · have := h (β * b / |S|) (by positivity)
      rw [← ha0] at this
      have hbb' : β * b ≠ 0 := hbb.ne'
      have hS' : |S| ≠ 0 := hS.ne'
      have hβ' : β ≠ 0 := by intro h0; rw [h0, zero_mul] at hbb'; exact hbb' rfl
      have hb' : b ≠ 0 := by intro h0; rw [h0, mul_zero] at hbb'; exact hbb' rfl
      have e : (β / 2) * (β * b / |S| * 0 + b / (β * b / |S|)) = |S| / 2 := by
        rw [mul_zero, zero_add]
        field_simp
      rw [e] at this
      linarith
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · rw [← hb0, Real.sqrt_zero, mul_zero]
    by_contra hS
    push Not at hS
    rcases eq_or_lt_of_le (mul_nonneg hβ ha) with hbb | hbb
    · have := h 1 one_pos
      rw [← hb0] at this
      have e : (β / 2) * (1 * a + 0 / 1) = (β * a) / 2 := by ring
      rw [e, ← hbb] at this
      linarith
    · have := h (|S| / (β * a)) (by positivity)
      rw [← hb0] at this
      have hbb' : β * a ≠ 0 := hbb.ne'
      have hβ' : β ≠ 0 := by intro h0; rw [h0, zero_mul] at hbb'; exact hbb' rfl
      have ha' : a ≠ 0 := hapos.ne'
      have e : (β / 2) * (|S| / (β * a) * a + 0 / (|S| / (β * a))) = |S| / 2 := by
        rw [zero_div, add_zero]
        field_simp
      rw [e] at this
      linarith
  · have hsa := Real.sqrt_pos.mpr hapos
    have hsb := Real.sqrt_pos.mpr hbpos
    have := h (Real.sqrt b / Real.sqrt a) (by positivity)
    set u := Real.sqrt a with hu
    set v := Real.sqrt b with hv
    have ha2 : u * u = a := Real.mul_self_sqrt ha
    have hb2 : v * v = b := Real.mul_self_sqrt hb
    have e : (β / 2) * (v / u * a + b / (v / u)) = β * u * v := by
      rw [← ha2, ← hb2]
      field_simp
      ring
    rw [e] at this
    exact this

theorem Sp_bil_le (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (A B : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |Sp U p A B| ≤ 68 * α₀ * Real.sqrt (plaqBondSq A p) * Real.sqrt (plaqBondSq B p) :=
  amgm_to_prod _ _ _ _ (by positivity) (plaqBondSq_nonneg A p) (plaqBondSq_nonneg B p)
    (fun s hs => Sp_amgm U hα₀ hpl A B p s hs)

/-! ## the plaquette sum -/

theorem card_dirs : Fintype.card PeriodicPlaquetteDirections = 3 := by decide

theorem pbs_sum_le (A : BondFnL2 L) :
    ∑ p : PeriodicLatticePlaquette L, plaqBondSq (WithLp.ofLp A) p ≤ 12 * ‖A‖ ^ 2 := by
  have hd : ∀ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L, plaqBondSq (WithLp.ofLp A) (x, d)
      ≤ 4 * ‖A‖ ^ 2 := by
    intro d
    unfold plaqBondSq
    simp only [Finset.sum_add_distrib]
    rw [sum_shift_site d.1.1 (fun y => ‖(WithLp.ofLp A) (y, d.1.2)‖ ^ 2),
      sum_shift_site d.1.2 (fun y => ‖(WithLp.ofLp A) (y, d.1.1)‖ ^ 2)]
    have h1 := sum_dir_le A d.1.1
    have h2 := sum_dir_le A d.1.2
    have e1 : ∀ ν, ∑ y : PeriodicLatticeSite L, ‖(WithLp.ofLp A) (y, ν)‖ ^ 2 = ∑ y : PeriodicLatticeSite L, ‖A (y, ν)‖ ^ 2 :=
      fun ν => rfl
    rw [e1, e1]
    linarith
  calc ∑ p : PeriodicLatticePlaquette L, plaqBondSq (WithLp.ofLp A) p
      = ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L, plaqBondSq (WithLp.ofLp A) (x, d) :=
        Fintype.sum_prod_type_right _
    _ ≤ ∑ _d : PeriodicPlaquetteDirections, 4 * ‖A‖ ^ 2 := Finset.sum_le_sum (fun d _ => hd d)
    _ = 12 * ‖A‖ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, card_dirs]; simp; ring

/-- `Δ'` as the plaquette sum of `Sp` -/
theorem DeltaPrime_eq_sum (U : Cfg L) (A B : BondFnL2 L) :
    AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U Set.univ A B
      = ∑ p : PeriodicLatticePlaquette L, Sp U p (WithLp.ofLp A) (WithLp.ofLp B) := by
  show AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc U Set.univ (WithLp.ofLp A) (WithLp.ofLp B) = _
  unfold AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul,
    AdalyFormal.StatementLaneR6.deltaPrimeBilRawLoc_apply, Set.mem_univ, if_true]
  unfold Sp
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- `Δ'` on the `L²` carrier -/
noncomputable def DpOp (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap (AdalyFormal.StatementLaneR6.deltaPrimeOpLoc U Set.univ)

theorem inner_DpOp (U : Cfg L) (x y : BondFnL2 L) :
    ⟪x, DpOp U y⟫ = ∑ p : PeriodicLatticePlaquette L, Sp U p (WithLp.ofLp x) (WithLp.ofLp y) := by
  show ⟪x, AdalyFormal.StatementLaneR6.deltaPrimeOpLoc U Set.univ y⟫ = _
  rw [AdalyFormal.StatementLaneR6.inner_deltaPrimeOpLoc, DeltaPrime_eq_sum]

theorem DpOp_symm (U : Cfg L) (x y : BondFnL2 L) : ⟪DpOp U x, y⟫ = ⟪x, DpOp U y⟫ := by
  rw [real_inner_comm, inner_DpOp, inner_DpOp]
  exact Finset.sum_congr rfl (fun p _ => Sp_symm U p _ _)

/-- the operator-norm bound from a bilinear bound -/
theorem opnorm_of_bil {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] (T : X →L[ℝ] X) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x y, |⟪x, T y⟫| ≤ C * ‖x‖ * ‖y‖) : ‖T‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC (fun y => ?_)
  have h1 := h (T y) y
  rw [real_inner_self_eq_norm_sq] at h1
  rw [abs_of_nonneg (sq_nonneg _)] at h1
  by_cases h0 : ‖T y‖ = 0
  · rw [h0]; positivity
  have hpos : 0 < ‖T y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  nlinarith

theorem sum_sqrt_bound (A B : BondFnL2 L) :
    ∑ p : PeriodicLatticePlaquette L, Real.sqrt (plaqBondSq (WithLp.ofLp A) p) * Real.sqrt (plaqBondSq (WithLp.ofLp B) p)
      ≤ 12 * ‖A‖ * ‖B‖ := by
  refine (Real.sum_sqrt_mul_sqrt_le _ (fun p => plaqBondSq_nonneg _ p) (fun p => plaqBondSq_nonneg _ p)).trans ?_
  have h1 := Real.sqrt_le_sqrt (pbs_sum_le A)
  have h2 := Real.sqrt_le_sqrt (pbs_sum_le B)
  have e : ∀ X : BondFnL2 L, Real.sqrt (12 * ‖X‖ ^ 2) = Real.sqrt 12 * ‖X‖ := by
    intro X; rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
  rw [e] at h1 h2
  calc _ ≤ (Real.sqrt 12 * ‖A‖) * (Real.sqrt 12 * ‖B‖) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = 12 * ‖A‖ * ‖B‖ := by
        rw [show Real.sqrt 12 * ‖A‖ * (Real.sqrt 12 * ‖B‖) = (Real.sqrt 12 * Real.sqrt 12) * (‖A‖ * ‖B‖) by ring,
          Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
        ring

theorem DpOp_norm (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U) :
    ‖DpOp U‖ ≤ 816 * α₀ := by
  refine opnorm_of_bil _ _ (by positivity) (fun x y => ?_)
  rw [inner_DpOp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p, |Sp U p (WithLp.ofLp x) (WithLp.ofLp y)|
      ≤ ∑ p : PeriodicLatticePlaquette L, 68 * α₀ * (Real.sqrt (plaqBondSq (WithLp.ofLp x) p)
          * Real.sqrt (plaqBondSq (WithLp.ofLp y) p)) :=
        Finset.sum_le_sum (fun p _ => by rw [← mul_assoc]; exact Sp_bil_le U hα₀ hpl _ _ p)
    _ = 68 * α₀ * ∑ p : PeriodicLatticePlaquette L, Real.sqrt (plaqBondSq (WithLp.ofLp x) p)
          * Real.sqrt (plaqBondSq (WithLp.ofLp y) p) := by rw [Finset.mul_sum]
    _ ≤ 68 * α₀ * (12 * ‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left (sum_sqrt_bound x y) (by positivity)
    _ = 816 * α₀ * ‖x‖ * ‖y‖ := by ring

/-! ## the weighted `Δ'` -/

/-- the per-plaquette rescaled field `x'_p(b) = e^{φ(b₀)−φ(p₀)} x(b)` -/
noncomputable def rescP (φ : PeriodicLatticeSite L → ℝ) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Bond L → SuTwo := fun b => Real.exp (φ b.1 - φ p.1) • A b

theorem wt_eq_resc (φ : PeriodicLatticeSite L → ℝ) (p : PeriodicLatticePlaquette L) (A : BondFnL2 L) :
    WithLp.ofLp (bondWt φ A) = Real.exp (φ p.1) • rescP φ p (WithLp.ofLp A) := by
  funext b
  show Real.exp (φ b.1) • A b = Real.exp (φ p.1) • (Real.exp (φ b.1 - φ p.1) • A b)
  rw [smul_smul, ← Real.exp_add]
  congr 2; ring

theorem pbs_resc_sub (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (p : PeriodicLatticePlaquette L)
    (A : Bond L → SuTwo) :
    plaqBondSq (rescP φ p A - A) p ≤ (Real.exp θ' - 1) ^ 2 * plaqBondSq A p := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  have hb : ∀ b : Bond L, |φ b.1 - φ p.1| ≤ θ' →
      ‖(rescP φ p A - A) b‖ ^ 2 ≤ (Real.exp θ' - 1) ^ 2 * ‖A b‖ ^ 2 := by
    intro b hbθ
    have e : (rescP φ p A - A) b = (Real.exp (φ b.1 - φ p.1) - 1) • A b := by
      simp only [rescP, Pi.sub_apply, sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h1 := abs_exp_sub_one_le_of _ _ hbθ
    have h2 : (Real.exp (φ b.1 - φ p.1) - 1) ^ 2 ≤ (Real.exp θ' - 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have z0 : |φ p.1 - φ p.1| ≤ θ' := by simp [hθ]
  have z1 : |φ (periodicLatticeShift p.1 p.2.1.1) - φ p.1| ≤ θ' := hφ p.1 p.2.1.1
  have z2 : |φ (periodicLatticeShift p.1 p.2.1.2) - φ p.1| ≤ θ' := hφ p.1 p.2.1.2
  unfold plaqBondSq
  have a1 := hb (p.1, p.2.1.1) z0
  have a2 := hb (p.1, p.2.1.2) z0
  have a3 := hb (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) z1
  have a4 := hb (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) z2
  nlinarith

theorem pbs_resc (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (p : PeriodicLatticePlaquette L)
    (A : Bond L → SuTwo) :
    plaqBondSq (rescP φ p A) p ≤ Real.exp θ' ^ 2 * plaqBondSq A p := by
  have hb : ∀ b : Bond L, |φ b.1 - φ p.1| ≤ θ' → ‖rescP φ p A b‖ ^ 2 ≤ Real.exp θ' ^ 2 * ‖A b‖ ^ 2 := by
    intro b hbθ
    simp only [rescP]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (φ b.1 - φ p.1) ≤ Real.exp θ' := Real.exp_le_exp.mpr (le_trans (le_abs_self _) hbθ)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le h1 2) (sq_nonneg _)
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have z0 : |φ p.1 - φ p.1| ≤ θ' := by simp [hθ]
  have z1 : |φ (periodicLatticeShift p.1 p.2.1.1) - φ p.1| ≤ θ' := hφ p.1 p.2.1.1
  have z2 : |φ (periodicLatticeShift p.1 p.2.1.2) - φ p.1| ≤ θ' := hφ p.1 p.2.1.2
  unfold plaqBondSq
  have a1 := hb (p.1, p.2.1.1) z0
  have a2 := hb (p.1, p.2.1.2) z0
  have a3 := hb (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) z1
  have a4 := hb (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) z2
  nlinarith

theorem DpOp_conj_bil (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (x y : BondFnL2 L) :
    |⟪x, bondWt φ (DpOp U (bondWt (-φ) y)) - DpOp U y⟫| ≤ 816 * α₀ * (Real.exp (2 * θ') - 1) * ‖x‖ * ‖y‖ := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  have hneg : WtLip θ' (-φ) := WtLip_neg θ' φ hφ
  rw [inner_sub_right, ← bondWt_symm, inner_DpOp, inner_DpOp, ← Finset.sum_sub_distrib]
  have hpt : ∀ p : PeriodicLatticePlaquette L,
      |Sp U p (WithLp.ofLp (bondWt φ x)) (WithLp.ofLp (bondWt (-φ) y)) - Sp U p (WithLp.ofLp x) (WithLp.ofLp y)|
        ≤ 68 * α₀ * (Real.exp (2 * θ') - 1) * (Real.sqrt (plaqBondSq (WithLp.ofLp x) p)
          * Real.sqrt (plaqBondSq (WithLp.ofLp y) p)) := by
    intro p
    set X := WithLp.ofLp x
    set Y := WithLp.ofLp y
    set X' := rescP φ p X
    set Y' := rescP (-φ) p Y
    have e1 : WithLp.ofLp (bondWt φ x) = Real.exp (φ p.1) • X' := wt_eq_resc φ p x
    have e2 : WithLp.ofLp (bondWt (-φ) y) = Real.exp ((-φ) p.1) • Y' := wt_eq_resc (-φ) p y
    rw [e1, e2, Sp_smul_left, Sp_smul_right, ← mul_assoc, ← Real.exp_add]
    have e3 : φ p.1 + (-φ) p.1 = 0 := by simp
    rw [e3, Real.exp_zero, one_mul]
    have e4 : Sp U p X' Y' - Sp U p X Y = Sp U p (X' - X) Y' + Sp U p X (Y' - Y) := by
      rw [Sp_sub_left, Sp_sub_right]; ring
    rw [e4]
    have b1 := Sp_bil_le U hα₀ hpl (X' - X) Y' p
    have b2 := Sp_bil_le U hα₀ hpl X (Y' - Y) p
    have s1 : Real.sqrt (plaqBondSq (X' - X) p) ≤ (Real.exp θ' - 1) * Real.sqrt (plaqBondSq X p) := by
      have := Real.sqrt_le_sqrt (pbs_resc_sub φ θ' hφ p X)
      rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ] at this
    have s2 : Real.sqrt (plaqBondSq Y' p) ≤ Real.exp θ' * Real.sqrt (plaqBondSq Y p) := by
      have := Real.sqrt_le_sqrt (pbs_resc (-φ) θ' hneg p Y)
      rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] at this
    have s3 : Real.sqrt (plaqBondSq (Y' - Y) p) ≤ (Real.exp θ' - 1) * Real.sqrt (plaqBondSq Y p) := by
      have := Real.sqrt_le_sqrt (pbs_resc_sub (-φ) θ' hneg p Y)
      rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ] at this
    have hx0 := Real.sqrt_nonneg (plaqBondSq X p)
    have hy0 := Real.sqrt_nonneg (plaqBondSq Y p)
    have hA0 : 0 ≤ 68 * α₀ := by positivity
    have c1 : |Sp U p (X' - X) Y'| ≤ 68 * α₀ * ((Real.exp θ' - 1) * Real.sqrt (plaqBondSq X p))
        * (Real.exp θ' * Real.sqrt (plaqBondSq Y p)) :=
      b1.trans (mul_le_mul (mul_le_mul_of_nonneg_left s1 hA0) s2 (Real.sqrt_nonneg _) (by positivity))
    have c2 : |Sp U p X (Y' - Y)| ≤ 68 * α₀ * Real.sqrt (plaqBondSq X p)
        * ((Real.exp θ' - 1) * Real.sqrt (plaqBondSq Y p)) :=
      b2.trans (mul_le_mul_of_nonneg_left s3 (by positivity))
    have e5 : Real.exp (2 * θ') = Real.exp θ' * Real.exp θ' := by rw [← Real.exp_add]; ring_nf
    refine (abs_add_le _ _).trans ((add_le_add c1 c2).trans (le_of_eq ?_))
    rw [e5]; ring
  calc |∑ p, (Sp U p (WithLp.ofLp (bondWt φ x)) (WithLp.ofLp (bondWt (-φ) y)) - Sp U p (WithLp.ofLp x) (WithLp.ofLp y))|
      ≤ ∑ p, |Sp U p (WithLp.ofLp (bondWt φ x)) (WithLp.ofLp (bondWt (-φ) y)) - Sp U p (WithLp.ofLp x) (WithLp.ofLp y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : PeriodicLatticePlaquette L, 68 * α₀ * (Real.exp (2 * θ') - 1) * (Real.sqrt (plaqBondSq (WithLp.ofLp x) p)
          * Real.sqrt (plaqBondSq (WithLp.ofLp y) p)) := Finset.sum_le_sum (fun p _ => hpt p)
    _ = 68 * α₀ * (Real.exp (2 * θ') - 1) * ∑ p : PeriodicLatticePlaquette L, Real.sqrt (plaqBondSq (WithLp.ofLp x) p)
          * Real.sqrt (plaqBondSq (WithLp.ofLp y) p) := by rw [Finset.mul_sum]
    _ ≤ 68 * α₀ * (Real.exp (2 * θ') - 1) * (12 * ‖x‖ * ‖y‖) := by
        have : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
        exact mul_le_mul_of_nonneg_left (sum_sqrt_bound x y) (by positivity)
    _ = 816 * α₀ * (Real.exp (2 * θ') - 1) * ‖x‖ * ‖y‖ := by ring

theorem DpOp_cjp_norm (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjp (bondWP φ) (bondWP φ) (DpOp U) - DpOp U‖ ≤ 816 * α₀ * (Real.exp (2 * θ') - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
  refine opnorm_of_bil _ _ (by positivity) (fun x y => ?_)
  rw [ContinuousLinearMap.sub_apply, cjp_apply]
  exact DpOp_conj_bil U hα₀ hpl φ θ' hφ x y

theorem DpOp_cjm_norm (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (φ : PeriodicLatticeSite L → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjm (bondWP φ) (bondWP φ) (DpOp U) - DpOp U‖ ≤ 816 * α₀ * (Real.exp (2 * θ') - 1) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
  refine opnorm_of_bil _ _ (by positivity) (fun x y => ?_)
  rw [ContinuousLinearMap.sub_apply]
  have e : cjm (bondWP φ) (bondWP φ) (DpOp U) y = bondWt (-φ) (DpOp U (bondWt (-(-φ)) y)) := by
    rw [neg_neg]; rfl
  rw [e]
  exact DpOp_conj_bil U hα₀ hpl (-φ) θ' (WtLip_neg θ' φ hφ) x y

/-! ## the decomposition `Δ = C*C + Δ'` (full tower) -/

theorem Delta_decomp (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (AdalyFormal.StatementLane.scaleUp ell k Lu)) :
    Delta (AdalyFormal.SliceCoerc.GF ell k Lu) U
      = ContinuousLinearMap.adjoint (curlC U) ∘L curlC U + DpOp U := by
  have hP : plaqIn (AdalyFormal.SliceCoerc.GF ell k Lu).Om0 = Set.univ := by
    rw [AdalyFormal.SliceCoerc.fullTower_Om0]; exact AdalyFormal.StatementLaneG.plaqIn_univ
  ext1 A
  refine ext_inner_left ℝ (fun x => ?_)
  rw [Delta, AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, hP, AdalyFormal.StatementLaneR6.plaqMask_univ,
    AdalyFormal.StatementLaneR6.plaqMask_univ, ContinuousLinearMap.add_apply, inner_add_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have h1 : ⟪x, DpOp U A⟫ = AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U Set.univ x A :=
    AdalyFormal.StatementLaneR6.inner_deltaPrimeOpLoc U Set.univ x A
  rw [h1]
  rfl

#print axioms curl_sq_le_pbs
#print axioms bilPlaq_quad_le
#print axioms Sp_amgm
#print axioms amgm_to_prod
#print axioms Sp_bil_le
#print axioms card_dirs
#print axioms pbs_sum_le
#print axioms DeltaPrime_eq_sum
#print axioms inner_DpOp
#print axioms DpOp_symm
#print axioms opnorm_of_bil
#print axioms sum_sqrt_bound
#print axioms DpOp_norm
#print axioms wt_eq_resc
#print axioms pbs_resc_sub
#print axioms pbs_resc
#print axioms DpOp_conj_bil
#print axioms DpOp_cjp_norm
#print axioms DpOp_cjm_norm
#print axioms Delta_decomp

end AdalyFormal.DLayer
