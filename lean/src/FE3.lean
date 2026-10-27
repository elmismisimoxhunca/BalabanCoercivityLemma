import GN10
import W1
import FE2

/-!
# FE3 -- FlatExt: an explicit right inverse of the FLAT top-level constraint map `Q'_k(1)` (full tower)

Objects (read-only, from the slice-coercivity lane and the tree): `Qtop (GF ell k Lu) (trivialU _)`
(`f ↦ (Q'_k(1) f)|_{Λ_k}`, GN6), `gradL2`, `coarseC`.  `n = ell^k`.

* `Qcomposite_flat`: at the trivial tower, `Q'_j λ (y) = (ell^{-3})^j Σ_{x ∈ blockOf y (ell^j)} λ x` for EVERY site `y`
  (blocks are coordinate boxes without wrap-around, as in the tree; no divisibility hypothesis).
* `flatE`: `(E w)(x) = Σ_{y ∈ Λ_k} (∏_μ phi(x_μ - y_μ)) • w y` (FE1's dual kernel, cyclic offsets).
* `flatE_rightInv`: `Qtop (GF ell k Lu) (trivialU _) (flatE w) = w` (0 < ell).
* `flatE_norm_sq`: `‖E w‖² ≤ 729 n³ ‖w‖²`;  `flatE_grad_norm_sq`: `‖D_1 E w‖² ≤ 78732 n ‖w‖²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.FlatExt

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF ubarTower_trivial)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf inBlock Bond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf inStepBlock stepAverage
  stepAverage_trivialU Qcomposite Qcomposite_succ)
open AdalyFormal.StatementLane (scaleUp)

section blocks
variable {L : PeriodicLatticeExtent}

theorem sum_stepBlock_blockOf {M : Type*} [AddCommMonoid M] (s ell : ℕ) (hs : 0 < s)
    (y : PeriodicLatticeSite L) (f : PeriodicLatticeSite L → M) :
    ∑ x ∈ stepBlockOf y s ell, ∑ x' ∈ blockOf x s, f x' = ∑ x' ∈ blockOf y (s * ell), f x' := by
  classical
  have hdisj : (↑(stepBlockOf y s ell) : Set (PeriodicLatticeSite L)).PairwiseDisjoint
      (fun x => blockOf x s) := by
    intro x1 hx1 x2 hx2 hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x' h1 h2
    apply hne
    rw [Finset.mem_coe, mem_stepBlockOf] at hx1 hx2
    rw [mem_blockOf] at h1 h2
    funext μ
    apply Fin.ext
    obtain ⟨a1, b1, ⟨p, hp⟩⟩ := hx1 μ
    obtain ⟨a2, b2, ⟨q, hq⟩⟩ := hx2 μ
    obtain ⟨c1, d1⟩ := h1 μ
    obtain ⟨c2, d2⟩ := h2 μ
    have e1 : s * p < s * (q + 1) := by rw [Nat.mul_succ]; omega
    have e2 : s * q < s * (p + 1) := by rw [Nat.mul_succ]; omega
    have f1 := Nat.lt_of_mul_lt_mul_left e1
    have f2 := Nat.lt_of_mul_lt_mul_left e2
    have hpq : p = q := by omega
    subst hpq
    omega
  have hU : (stepBlockOf y s ell).biUnion (fun x => blockOf x s) = blockOf y (s * ell) := by
    ext x'
    simp only [Finset.mem_biUnion, mem_stepBlockOf, mem_blockOf]
    constructor
    · rintro ⟨x, hx, hx'⟩ μ
      obtain ⟨a, b, ⟨p, hp⟩⟩ := hx μ
      obtain ⟨c, d⟩ := hx' μ
      have h1 : s * p < s * ell := by omega
      have h2 : p + 1 ≤ ell := Nat.lt_of_mul_lt_mul_left h1
      have h3 : s * (p + 1) ≤ s * ell := Nat.mul_le_mul_left s h2
      rw [Nat.mul_succ] at h3
      constructor <;> omega
    · intro hx'
      refine ⟨fun μ => ⟨(y μ).val + s * (((x' μ).val - (y μ).val) / s), ?_⟩, fun μ => ?_, fun μ => ?_⟩
      · have hm := Nat.mul_div_le ((x' μ).val - (y μ).val) s
        have h1 := hx' μ
        have h2 := (x' μ).isLt
        omega
      · have hm := Nat.mul_div_le ((x' μ).val - (y μ).val) s
        obtain ⟨c, d⟩ := hx' μ
        refine ⟨by simp only; omega, by simp only; omega, ⟨((x' μ).val - (y μ).val) / s, by simp only; omega⟩⟩
      · have hm := Nat.mul_div_le ((x' μ).val - (y μ).val) s
        have hl := Nat.lt_mul_div_succ ((x' μ).val - (y μ).val) hs
        rw [Nat.mul_succ] at hl
        obtain ⟨c, d⟩ := hx' μ
        simp only
        constructor <;> omega
  rw [← hU, Finset.sum_biUnion hdisj]

theorem blockOf_one (y : PeriodicLatticeSite L) : blockOf y 1 = {y} := by
  ext x
  simp only [mem_blockOf, Finset.mem_singleton]
  constructor
  · intro h
    funext μ
    apply Fin.ext
    have := h μ
    omega
  · rintro rfl μ
    omega

/-- **Flat composite, closed form.** -/
theorem Qcomposite_flat (ell : ℕ) (hell : 0 < ell) (j : ℕ) (lam : PeriodicLatticeSite L → SuTwo)
    (y : PeriodicLatticeSite L) :
    Qcomposite (fun _ => trivialU L) ell j lam y
      = ((1 / (ell : ℝ) ^ 3) ^ j) • ∑ x ∈ blockOf y (ell ^ j), lam x := by
  induction j generalizing y with
  | zero =>
      rw [pow_zero, pow_zero, one_smul, blockOf_one, Finset.sum_singleton]
      rfl
  | succ j ih =>
      rw [Qcomposite_succ, stepAverage_trivialU]
      simp_rw [ih]
      rw [← Finset.smul_sum, smul_smul, sum_stepBlock_blockOf _ _ (pow_pos hell j), ← pow_succ]
      congr 1
      ring

end blocks

/-! ## the top-level flat map -/

theorem Qtop_flat (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (f : SiteL2 (scaleUp ell k Lu)) (y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) :
    Qtop (GF ell k Lu) (trivialU _) f y = ((1 / (ell : ℝ) ^ 3) ^ k) • ∑ x ∈ blockOf y.1 (ell ^ k), f x := by
  have hbg : bgTower (GF ell k Lu) (trivialU _) = fun _ => trivialU _ :=
    funext (ubarTower_trivial ell)
  show Qlev (GF ell k Lu) (trivialU _) (GF ell k Lu).k y.1 f = _
  rw [Qlev_apply, hbg]
  exact Qcomposite_flat ell hell k _ y.1

/-- the tensor kernel `ψ(x,y) = ∏_μ phi(x_μ - y_μ)`. -/
noncomputable def psi (ell k : ℕ) (Lu : PeriodicLatticeExtent) (x y : PeriodicLatticeSite (scaleUp ell k Lu)) : ℝ :=
  ∏ μ : Fin 3, phi (ell ^ k) (Lu μ + 1) (x μ - y μ).val

/-- its majorant `Ξ(x,y) = ∏_μ chi(x_μ - y_μ)`. -/
noncomputable def Xi (ell k : ℕ) (Lu : PeriodicLatticeExtent) (x y : PeriodicLatticeSite (scaleUp ell k Lu)) : ℝ :=
  ∏ μ : Fin 3, chi (ell ^ k) (Lu μ + 1) (x μ - y μ).val

/-- **FlatExt**: `(E w)(x) = Σ_{y ∈ Λ_k} ψ(x,y) • w(y)`. -/
noncomputable def flatE (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    coarseC (GF ell k Lu) →L[ℝ] SiteL2 (scaleUp ell k Lu) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun x =>
        ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, psi ell k Lu x y.1 • w y)
      map_add' := fun w1 w2 => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.add_apply, smul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by
        refine PiLp.ext (fun x => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_comm c] }

theorem flatE_apply (ell k : ℕ) (Lu : PeriodicLatticeExtent) (w : coarseC (GF ell k Lu))
    (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    flatE ell k Lu w x = ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, psi ell k Lu x y.1 • w y := rfl

theorem dvd_of_lam (ell k : ℕ) (Lu : PeriodicLatticeExtent)
    (y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) (μ : Fin 3) : ell ^ k ∣ (y.1 μ).val :=
  (fullTower_lam_k ell k Lu y.1).mp y.2 μ

theorem block_sum_psi (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (y' y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) :
    ∑ x ∈ blockOf y'.1 (ell ^ k), psi ell k Lu x y.1 = if y' = y then ((ell : ℝ) ^ k) ^ 3 else 0 := by
  classical
  have hn : 0 < ell ^ k := pow_pos hell k
  have hpi : blockOf y'.1 (ell ^ k) = Fintype.piFinset (fun μ => Finset.univ.filter
      (fun a : Fin (scaleUp ell k Lu μ + 1) => (y'.1 μ).val ≤ a.val ∧ a.val < (y'.1 μ).val + ell ^ k)) := by
    ext x
    simp only [mem_blockOf, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and, inBlock]
  rw [hpi]
  unfold psi
  refine (Finset.prod_univ_sum _ (fun μ (a : Fin (scaleUp ell k Lu μ + 1)) =>
    phi (ell ^ k) (Lu μ + 1) (a - y.1 μ).val)).symm.trans ?_
  have hfac : ∀ μ : Fin 3, ∑ a ∈ Finset.univ.filter
      (fun a : Fin (scaleUp ell k Lu μ + 1) => (y'.1 μ).val ≤ a.val ∧ a.val < (y'.1 μ).val + ell ^ k),
      phi (ell ^ k) (Lu μ + 1) (a - y.1 μ).val = if y'.1 μ = y.1 μ then ((ell ^ k : ℕ) : ℝ) else 0 :=
    fun μ => block_mean (Lu μ + 1) (ell ^ k) hn (scaleUp_succ ell k Lu hell μ) (y.1 μ) (y'.1 μ)
      (dvd_of_lam ell k Lu y μ) (dvd_of_lam ell k Lu y' μ)
  rw [Finset.prod_congr rfl (fun μ _ => hfac μ), Finset.prod_ite_zero]
  have hiff : (∀ μ ∈ (Finset.univ : Finset (Fin 3)), y'.1 μ = y.1 μ) ↔ y' = y := by
    constructor
    · intro h; exact Subtype.ext (funext fun μ => h μ (Finset.mem_univ μ))
    · rintro rfl μ _; rfl
  simp only [hiff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl

/-- **`Q'_k(1) E = id`.** -/
theorem flatE_rightInv (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (w : coarseC (GF ell k Lu)) : Qtop (GF ell k Lu) (trivialU _) (flatE ell k Lu w) = w := by
  classical
  refine PiLp.ext (fun y' => ?_)
  rw [Qtop_flat ell k Lu hell]
  simp only [flatE_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  simp only [block_sum_psi ell k Lu hell, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [smul_smul]
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have h1 : (1 / (ell : ℝ) ^ 3) ^ k * ((ell : ℝ) ^ k) ^ 3 = 1 := by
    rw [div_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm 3 k]
    field_simp
  rw [h1, one_smul]

/-! ## norms (Schur) -/

theorem abs_psi_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (x y : PeriodicLatticeSite (scaleUp ell k Lu)) : |psi ell k Lu x y| ≤ Xi ell k Lu x y :=
  abs_prod_le_prod _ _ (fun μ => abs_phi_le _ _ _ (pow_pos hell k))

theorem Xi_nonneg (ell k : ℕ) (Lu : PeriodicLatticeExtent) (x y : PeriodicLatticeSite (scaleUp ell k Lu)) :
    0 ≤ Xi ell k Lu x y :=
  Finset.prod_nonneg (fun μ _ => chi_nonneg _ _ _)

theorem row_Xi_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, Xi ell k Lu x y.1 ≤ 27 := by
  classical
  have hs : ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, Xi ell k Lu x y.1
      = ∑ y ∈ Finset.univ.filter (fun y => y ∈ (GF ell k Lu).Lam (GF ell k Lu).k), Xi ell k Lu x y :=
    (Finset.sum_subtype _ (by simp) _).symm
  rw [hs, Finset.sum_filter]
  have hpt : ∀ y : PeriodicLatticeSite (scaleUp ell k Lu),
      (if y ∈ (GF ell k Lu).Lam (GF ell k Lu).k then Xi ell k Lu x y else 0)
        = ∏ μ : Fin 3, (if ell ^ k ∣ (y μ).val then chi (ell ^ k) (Lu μ + 1) (x μ - y μ).val else 0) := by
    intro y
    rw [Finset.prod_ite_zero]
    have hiff : y ∈ (GF ell k Lu).Lam (GF ell k Lu).k ↔ ∀ μ ∈ (Finset.univ : Finset (Fin 3)), ell ^ k ∣ (y μ).val :=
      (fullTower_lam_k ell k Lu y).trans ⟨fun h μ _ => h μ, fun h μ => h μ (Finset.mem_univ _)⟩
    by_cases h : y ∈ (GF ell k Lu).Lam (GF ell k Lu).k
    · rw [if_pos h, if_pos (hiff.mp h)]; rfl
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  simp only [hpt]
  rw [← Fintype.piFinset_univ]
  refine (Finset.prod_univ_sum _ (fun μ (a : Fin (scaleUp ell k Lu μ + 1)) =>
    if ell ^ k ∣ a.val then chi (ell ^ k) (Lu μ + 1) (x μ - a).val else 0)).symm.trans_le ?_
  calc ∏ μ : Fin 3, ∑ a ∈ (Finset.univ : Finset (Fin (scaleUp ell k Lu μ + 1))),
        (if ell ^ k ∣ a.val then chi (ell ^ k) (Lu μ + 1) (x μ - a).val else 0)
      ≤ ∏ _μ : Fin 3, (3 : ℝ) := by
        refine Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg (fun a _ => ?_)) (fun μ _ => ?_)
        · split_ifs
          · exact chi_nonneg _ _ _
          · exact le_refl 0
        · have hd : ell ^ k ∣ scaleUp ell k Lu μ + 1 := ⟨Lu μ + 1, by rw [scaleUp_succ ell k Lu hell μ, mul_comm]⟩
          exact row_chi_le (ell ^ k) (Lu μ + 1) hd (x μ)
    _ = 27 := by norm_num [Finset.prod_const]

theorem col_Xi_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (y : PeriodicLatticeSite (scaleUp ell k Lu)) :
    ∑ x : PeriodicLatticeSite (scaleUp ell k Lu), Xi ell k Lu x y ≤ 27 * ((ell : ℝ) ^ k) ^ 3 := by
  classical
  unfold Xi
  rw [← Fintype.piFinset_univ]
  refine (Finset.prod_univ_sum _ (fun μ (a : Fin (scaleUp ell k Lu μ + 1)) =>
    chi (ell ^ k) (Lu μ + 1) (a - y μ).val)).symm.trans_le ?_
  calc ∏ μ : Fin 3, ∑ a ∈ (Finset.univ : Finset (Fin (scaleUp ell k Lu μ + 1))),
        chi (ell ^ k) (Lu μ + 1) (a - y μ).val
      ≤ ∏ _μ : Fin 3, (3 * ((ell ^ k : ℕ) : ℝ)) :=
        Finset.prod_le_prod (fun μ _ => Finset.sum_nonneg (fun a _ => chi_nonneg _ _ _))
          (fun μ _ => col_chi_le (ell ^ k) (Lu μ + 1) (pow_pos hell k) (y μ))
    _ = 27 * ((ell : ℝ) ^ k) ^ 3 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring

/-- **`‖E w‖² ≤ 729 n³ ‖w‖²`**, `n = ell^k`. -/
theorem flatE_norm_sq (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (w : coarseC (GF ell k Lu)) :
    ‖flatE ell k Lu w‖ ^ 2 ≤ 729 * ((ell : ℝ) ^ k) ^ 3 * ‖w‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [flatE_apply]
  have := schur (fun x (y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) => psi ell k Lu x y.1)
    (fun x y => Xi ell k Lu x y.1) (fun x y => abs_psi_le ell k Lu hell x y.1) 27 (27 * ((ell : ℝ) ^ k) ^ 3)
    (by norm_num) (fun x => row_Xi_le ell k Lu hell x)
    (fun y => col_Xi_le ell k Lu hell y.1) (fun y => w y)
  calc _ ≤ 27 * (27 * ((ell : ℝ) ^ k) ^ 3) * ∑ y, ‖w y‖ ^ 2 := this
    _ = 729 * ((ell : ℝ) ^ k) ^ 3 * ∑ y, ‖w y‖ ^ 2 := by ring

theorem gradL2_trivial_apply {L : PeriodicLatticeExtent} (f : SiteL2 L) (b : Bond L) :
    (gradL2 (trivialU L) f) b = f (periodicLatticeShift b.1 b.2) - f b.1 := by
  show gradValueCovariant (trivialU L) (WithLp.ofLp f) b = _
  simp [gradValueCovariant, trivialU, AdalyFormal.Balaban.CovariantOperators.RMap_one]

theorem abs_psi_shift_sub_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (x y : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3) :
    |psi ell k Lu (periodicLatticeShift x μ) y - psi ell k Lu x y| ≤ 6 / ((ell : ℝ) ^ k) * Xi ell k Lu x y := by
  have hn : 0 < ell ^ k := pow_pos hell k
  have hc : (0 : ℝ) ≤ 6 / ((ell : ℝ) ^ k) := by positivity
  unfold psi Xi
  have := abs_prod3_update_sub (fun ν => phi (ell ^ k) (Lu ν + 1) (x ν - y ν).val)
    (fun ν => phi (ell ^ k) (Lu ν + 1) ((periodicLatticeShift x μ) ν - y ν).val)
    (fun ν => chi (ell ^ k) (Lu ν + 1) (x ν - y ν).val) μ (6 / ((ell : ℝ) ^ k)) hc
    (fun ν hν => by simp only [periodicLatticeShift, Function.update_of_ne hν])
    (fun ν => abs_phi_le _ _ _ hn)
    (by
      simp only [periodicLatticeShift, Function.update_self]
      have h := abs_phi_step_fin (Lu μ + 1) (ell ^ k) hn (scaleUp_succ ell k Lu hell μ) (x μ) (y μ)
      push_cast at h
      exact h)
  exact this

/-- **`‖D_1 E w‖² ≤ 78732 n ‖w‖²`**, `n = ell^k`. -/
theorem flatE_grad_norm_sq (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (w : coarseC (GF ell k Lu)) :
    ‖gradL2 (trivialU _) (flatE ell k Lu w)‖ ^ 2 ≤ 78732 * (ell : ℝ) ^ k * ‖w‖ ^ 2 := by
  have hnr : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [gradL2_trivial_apply, flatE_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hμ : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite (scaleUp ell k Lu),
      ‖∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, psi ell k Lu (periodicLatticeShift x μ) y.1 • w y
        - ∑ y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}, psi ell k Lu x y.1 • w y‖ ^ 2
      ≤ 26244 * (ell : ℝ) ^ k * ∑ y, ‖w y‖ ^ 2 := by
    intro μ
    simp_rw [← Finset.sum_sub_distrib, ← sub_smul]
    have := schur (fun x (y : {y // y ∈ (GF ell k Lu).Lam (GF ell k Lu).k}) =>
        psi ell k Lu (periodicLatticeShift x μ) y.1 - psi ell k Lu x y.1)
      (fun x y => 6 / ((ell : ℝ) ^ k) * Xi ell k Lu x y.1)
      (fun x y => abs_psi_shift_sub_le ell k Lu hell x y.1 μ)
      (6 / ((ell : ℝ) ^ k) * 27) (6 / ((ell : ℝ) ^ k) * (27 * ((ell : ℝ) ^ k) ^ 3)) (by positivity)
      (fun x => by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (row_Xi_le ell k Lu hell x) (by positivity))
      (fun y => by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (col_Xi_le ell k Lu hell y.1) (by positivity))
      (fun y => w y)
    calc _ ≤ 6 / ((ell : ℝ) ^ k) * 27 * (6 / ((ell : ℝ) ^ k) * (27 * ((ell : ℝ) ^ k) ^ 3)) * ∑ y, ‖w y‖ ^ 2 := this
      _ = 26244 * (ell : ℝ) ^ k * ∑ y, ‖w y‖ ^ 2 := by field_simp [hnr.ne']; ring
  calc _ ≤ ∑ _μ : Fin 3, 26244 * (ell : ℝ) ^ k * ∑ y, ‖w y‖ ^ 2 := Finset.sum_le_sum (fun μ _ => hμ μ)
    _ = 78732 * (ell : ℝ) ^ k * ∑ y, ‖w y‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp only [nsmul_eq_mul]; push_cast; ring

theorem norm_le_of_sq (C : ℝ) (hC : 0 ≤ C) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ C * b ^ 2) :
    a ≤ Real.sqrt C * b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, ← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt h

theorem flatE_norm_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (w : coarseC (GF ell k Lu)) :
    ‖flatE ell k Lu w‖ ≤ Real.sqrt (729 * ((ell : ℝ) ^ k) ^ 3) * ‖w‖ :=
  norm_le_of_sq _ (by positivity) (norm_nonneg _) (norm_nonneg _) (flatE_norm_sq ell k Lu hell w)

theorem flatE_grad_norm_le (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (w : coarseC (GF ell k Lu)) :
    ‖gradL2 (trivialU _) (flatE ell k Lu w)‖ ≤ Real.sqrt (78732 * (ell : ℝ) ^ k) * ‖w‖ :=
  norm_le_of_sq _ (by positivity) (norm_nonneg _) (norm_nonneg _) (flatE_grad_norm_sq ell k Lu hell w)

#print axioms sum_stepBlock_blockOf
#print axioms Qcomposite_flat
#print axioms Qtop_flat
#print axioms block_sum_psi
#print axioms flatE_rightInv
#print axioms row_Xi_le
#print axioms col_Xi_le
#print axioms flatE_norm_sq
#print axioms abs_psi_shift_sub_le
#print axioms flatE_grad_norm_sq
#print axioms flatE_norm_le
#print axioms flatE_grad_norm_le

end AdalyFormal.FlatExt
