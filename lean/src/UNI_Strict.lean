import UNI_Joint
import ZR2B2

/-!
# UNI_Strict -- the hypothesis class of the union headline is strictly larger than that of the box headline (lane union_cubes_20261018)

Setting: `3 ≤ ell ≤ 10`, the full tower on `scaleUp ell k Lu` with `Lu μ + 1 = ell^(m+1)` (so each side is `ell` level-`k` blocks of side `b = M ℓ^k`, `M = ell^m`), `U★` = the "Wilson seam": `U★(y,2) = -1` if `y_2 = L_2` (the last layer) and `U★ = 1` on every other bond.
* `no_box_family`: if `a₀ ell^(m+1) ≤ 1` then NO family `F'` of triples (members with `10 ≤ f`, `f M α₀ ≤ a₀`) satisfies the box-class hypothesis `ClassCoupledP boxClass` for `U★`: a box cube of factor `f ≥ 10 ≥ ell` and index `k` is the whole torus, and
  regularity on the whole torus makes the holonomy of `U★` around the 2-cycle (`= -1`, `dist1 = 2√2`) a product of `ell^(m+1+k)` elements within `ell^(-k) a₀` of `1`.
* `unionFam_coupled`: the family of unions `C_x` (one or two blocks per direction around `x`) satisfies `ClassCoupledU` for `U★`: coverage of sites and plaquettes, and regularity (gauge `±1`, `A = 0`) on each `C_x`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace UNI.Strict

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoLogExp (su2NegOne)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open UNI.AllC UNI.Total UNI.Joint

/-- the Wilson seam. -/
noncomputable def Ustar (L : PeriodicLatticeExtent) : LinkCfg L :=
  fun e => if e.2 = 2 ∧ (e.1 2).val = L 2 then su2NegOne else 1

/-- the point on the 2-axis at height `i` (mod the side). -/
def pt (L : PeriodicLatticeExtent) (i : ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨if μ = 2 then i % (L μ + 1) else 0, by split_ifs; exact Nat.mod_lt _ (Nat.succ_pos _); exact Nat.succ_pos _⟩

theorem shift_pt (L : PeriodicLatticeExtent) (i : ℕ) : periodicLatticeShift (pt L i) 2 = pt L (i + 1) := by
  funext ν
  apply Fin.ext
  by_cases h : ν = 2
  · subst h
    simp only [periodicLatticeShift, Function.update_self, AdalyFormal.Thin.fin_add_one_val, pt, if_true]
    rw [Nat.mod_add_mod]
  · simp [periodicLatticeShift, Function.update_of_ne h, pt, h]

theorem pt_wrap (L : PeriodicLatticeExtent) : pt L (L 2 + 1) = pt L 0 := by
  funext ν; apply Fin.ext
  by_cases h : ν = 2
  · subst h; simp [pt]
  · simp [pt, h]

/-- partial holonomy of a link configuration along the 2-axis. -/
noncomputable def hol {L : PeriodicLatticeExtent} (U : LinkCfg L) : ℕ → G2
  | 0 => 1
  | n + 1 => hol U n * U (pt L n, 2)

theorem dist1_one : dist1 (1 : G2) = 0 := by
  unfold dist1; simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]

theorem hol_gauge {L : PeriodicLatticeExtent} (g : PeriodicLatticeSite L → G2) (U : LinkCfg L) (n : ℕ) :
    hol (periodicGaugeTransform g U) n = g (pt L 0) * hol U n * (g (pt L n))⁻¹ := by
  induction n with
  | zero => simp [hol]
  | succ n ih =>
    simp only [hol]
    rw [ih]
    have : periodicGaugeTransform g U (pt L n, 2) = g (pt L n) * U (pt L n, 2) * (g (pt L (n + 1)))⁻¹ := by
      unfold periodicGaugeTransform
      simp only [shift_pt]
    rw [this]
    group

theorem hol_ustar_le (L : PeriodicLatticeExtent) (n : ℕ) (hn : n ≤ L 2) : hol (Ustar L) n = 1 := by
  induction n with
  | zero => simp [hol]
  | succ n ih =>
    simp only [hol]
    rw [ih (by omega)]
    have : Ustar L (pt L n, 2) = 1 := by
      unfold Ustar
      have : ¬ ((pt L n 2).val = L 2) := by
        simp only [pt, if_true]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [this]
    rw [this]; simp

theorem hol_ustar_full (L : PeriodicLatticeExtent) : hol (Ustar L) (L 2 + 1) = su2NegOne := by
  simp only [hol]
  rw [hol_ustar_le L (L 2) le_rfl]
  have : Ustar L (pt L (L 2), 2) = su2NegOne := by
    unfold Ustar
    have : (pt L (L 2) 2).val = L 2 := by
      simp only [pt, if_true]
      exact Nat.mod_eq_of_lt (Nat.lt_succ_self _)
    simp [this]
  rw [this]; simp

theorem dist1_hol_le {L : PeriodicLatticeExtent} (U : LinkCfg L) (r : ℝ) (hr : ∀ i, dist1 (U (pt L i, 2)) ≤ r) (n : ℕ) :
    dist1 (hol U n) ≤ n * r := by
  induction n with
  | zero => simp [hol, dist1_one]
  | succ n ih =>
    simp only [hol]
    have := dist1_mul (hol U n) (U (pt L n, 2))
    have := hr n
    push_cast
    linarith

theorem no_box_family (ell m k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell) (hell10 : ell ≤ 10)
    (hLu : ∀ μ : Fin 3, Lu μ + 1 = ell ^ (m + 1)) {α₀ a₀ : ℝ} (ha : a₀ * (ell : ℝ) ^ (m + 1) ≤ 1)
    (F : CubeFam (scaleUp ell k Lu))
    (hF : ∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
      10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) :
    ¬ ClassCoupledP boxClass ell (ell ^ m) F k (fullTower ell k Lu) α₀ (((ell : ℝ) ^ k)⁻¹) (Ustar (scaleUp ell k Lu)) := by
  rintro ⟨c1, -, c3⟩
  have hell0 : 0 < ell := by omega
  set L := scaleUp ell k Lu with hL
  have hN : ∀ μ : Fin 3, L μ + 1 = ell * bigSide (ell ^ m) ell k := by
    intro μ
    have h1 : L μ + 1 = (Lu μ + 1) * ell ^ k := by
      rw [hL]; unfold scaleUp
      have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    rw [h1, hLu μ]; unfold bigSide; ring
  have hb0 : 0 < bigSide (ell ^ m) ell k := Nat.mul_pos (pow_pos hell0 m) (pow_pos hell0 k)
  have hx0 : pt L 0 ∈ (fullTower ell k Lu).Om 0 := by simp [fullTower]
  obtain ⟨sites, j, ⟨f, hf, hcls⟩, -⟩ := c1 _ hx0
  obtain ⟨hf10, hfsm⟩ := hF _ _ _ hf
  have hcls' : IsClassCube ell (ell ^ m) f k (fullTower ell k Lu) sites j := hcls
  obtain ⟨⟨hjk, ⟨z, -, hzs⟩, -, ⟨y, -, hy2⟩⟩, -⟩ := hcls'
  have hjk' : j = k := by
    by_contra hne
    have hlt : j + 1 ≤ k := by omega
    have : y ∈ (fullTower ell k Lu).Om (j + 1) := by simp [fullTower, hlt]
    exact hy2.2 this
  subst hjk'
  have hall : ∀ y : PeriodicLatticeSite L, y ∈ sites := by
    intro y
    rw [hzs]
    intro μ
    have h1 : ((y μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < L μ + 1 := Nat.mod_lt _ (Nat.succ_pos _)
    have h2 : L μ + 1 ≤ f * bigSide (ell ^ m) ell j := by
      rw [hN μ]
      calc ell * bigSide (ell ^ m) ell j ≤ 10 * bigSide (ell ^ m) ell j := Nat.mul_le_mul_right _ hell10
        _ ≤ f * bigSide (ell ^ m) ell j := Nat.mul_le_mul_right _ hf10
    show ((y μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < f * bigSide (ell ^ m) ell j
    exact lt_of_lt_of_le h1 h2
  obtain ⟨g, A, h1, -, -⟩ := c3 f sites j hf hcls
  -- a_0 is positive and at most 1
  set η : ℝ := ((ell : ℝ) ^ j)⁻¹ with hη
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
  have hpow : (1 : ℝ) ≤ (ell : ℝ) ^ j := one_le_pow₀ hellR
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := inv_le_one_of_one_le₀ hpow
  have hpm : (1 : ℝ) ≤ (ell : ℝ) ^ (m + 1) := one_le_pow₀ hellR
  have hscale : ((ell : ℝ) ^ j * η)⁻¹ = 1 := by rw [hη]; field_simp
  have hr : ∀ i, dist1 (periodicGaugeTransform g (Ustar L) (pt L i, 2)) ≤ η * a₀ := by
    intro i
    obtain ⟨hA, hg, hlt⟩ := h1 (pt L i, 2) ⟨hall _, hall _⟩
    rw [hscale, pow_one, mul_one] at hlt
    have hAn : frobNorm (A (pt L i, 2)) ≤ a₀ := le_trans hlt.le hfsm
    have ha0 : 0 < a₀ := lt_of_le_of_lt (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (lt_of_lt_of_le hlt hfsm)
    have ha1 : a₀ ≤ 1 := by nlinarith
    have hc : |η| * frobNorm (A (pt L i, 2)) ≤ 1 := by
      rw [abs_of_pos hη0]; nlinarith [AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg (A (pt L i, 2))]
    have := frob_exp_sub_one_le hA η hc (periodicGaugeTransform g (Ustar L) (pt L i, 2)) hg
    unfold dist1
    rw [abs_of_pos hη0] at this
    exact this.trans (mul_le_mul_of_nonneg_left hAn hη0.le)
  have hd := dist1_hol_le (periodicGaugeTransform g (Ustar L)) (η * a₀) hr (L 2 + 1)
  rw [hol_gauge, pt_wrap, hol_ustar_full, conj_negOne, dist1_negOne] at hd
  -- numerics: (L 2 + 1) η a₀ = ell^(m+1) a₀ ≤ 1
  have hNr : ((L 2 + 1 : ℕ) : ℝ) * η = (ell : ℝ) ^ (m + 1) := by
    rw [hN 2, hη]
    unfold bigSide
    push_cast
    field_simp
    ring
  have h2 : Real.sqrt 2 ≥ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have : ((L 2 + 1 : ℕ) : ℝ) * (η * a₀) ≤ 1 := by
    rw [← mul_assoc, hNr]; linarith [ha]
  linarith

/-! ## the union family `C_x` and its regularity for the Wilson seam -/

/-- one or two consecutive level-`k` blocks in each direction: the blocks of `x` and of `x + e_σ`. -/
def Cx {L : PeriodicLatticeExtent} (b : ℕ) (x : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) :=
  {y | ∀ σ : Fin 3, (y σ).val / b = (x σ).val / b ∨ (y σ).val / b = ((x σ).val + 1) % (L σ + 1) / b}

theorem blockClosed_Cx {L : PeriodicLatticeExtent} (b : ℕ) (x : PeriodicLatticeSite L) : BlockClosed b (Cx b x) := by
  intro y hy z hz σ
  rw [hz σ]; exact hy σ

theorem mem_Cx_of_forward {L : PeriodicLatticeExtent} (b : ℕ) (x y : PeriodicLatticeSite L)
    (h : ∀ σ, y σ = x σ ∨ y σ = x σ + 1) : y ∈ Cx b x := by
  intro σ
  rcases h σ with h | h
  · left; rw [h]
  · right; rw [h, AdalyFormal.Thin.fin_add_one_val]

theorem blk_next {ell b v : ℕ} (hb : 0 < b) (hv : v < ell * b) :
    ((v + 1) % (ell * b)) / b = v / b ∨ (v / b + 1 < ell ∧ ((v + 1) % (ell * b)) / b = v / b + 1) ∨
      (v / b = ell - 1 ∧ ((v + 1) % (ell * b)) / b = 0 ∧ v + 1 = ell * b) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < b ∧ v = b * q + r :=
    ⟨v / b, v % b, Nat.mod_lt _ hb, (Nat.div_add_mod v b).symm⟩
  have hq : (b * q + r) / b = q := by rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, add_zero]
  rw [hq]
  have e3 : b * ell = ell * b := mul_comm b ell
  have hql : q < ell := by
    by_contra h
    push Not at h
    have := Nat.mul_le_mul_left b h
    omega
  have e1 : b * (q + 1) = b * q + b := by ring
  have e2 := Nat.mul_le_mul_left b (by omega : q + 1 ≤ ell)
  by_cases h1 : r + 1 < b
  · left
    have hlt : b * q + r + 1 < ell * b := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have : b * q + r + 1 = b * q + (r + 1) := by ring
    rw [this, Nat.mul_add_div hb, Nat.div_eq_of_lt h1, add_zero]
  · have hrb : r + 1 = b := by omega
    have hv1 : b * q + r + 1 = b * (q + 1) := by omega
    by_cases h2 : q + 1 < ell
    · right; left
      refine ⟨h2, ?_⟩
      have e4 := Nat.mul_lt_mul_of_pos_left h2 hb
      have hlt : b * q + r + 1 < ell * b := by omega
      rw [Nat.mod_eq_of_lt hlt, hv1, Nat.mul_div_cancel_left _ hb]
    · right; right
      have hpe : q + 1 = ell := by omega
      have hve : b * q + r + 1 = ell * b := by rw [hv1, hpe, mul_comm]
      refine ⟨by omega, ?_, hve⟩
      rw [hve, Nat.mod_self, Nat.zero_div]

/-- the gauge on `C_x` that absorbs the seam. -/
noncomputable def gx {L : PeriodicLatticeExtent} (ell b : ℕ) (x : PeriodicLatticeSite L) (y : PeriodicLatticeSite L) : G2 :=
  if (x 2).val / b = ell - 1 ∧ (y 2).val / b = 0 then su2NegOne else 1

theorem su2NegOne_mul_self : (su2NegOne : G2) * su2NegOne = 1 := by apply Subtype.ext; simp

theorem su2NegOne_inv : (su2NegOne : G2)⁻¹ = su2NegOne :=
  inv_eq_of_mul_eq_one_right su2NegOne_mul_self

theorem gauge_bond_trivial {L : PeriodicLatticeExtent} {ell b : ℕ} (hb : 0 < b) (hell : 3 ≤ ell)
    (hNb : ∀ σ : Fin 3, L σ + 1 = ell * b) (x : PeriodicLatticeSite L) {e : Bond L} (he : CubeBond (Cx b x) e) :
    periodicGaugeTransform (gx ell b x) (Ustar L) e = 1 := by
  obtain ⟨y, σ⟩ := e
  obtain ⟨hy, hy'⟩ := he
  show gx ell b x y * Ustar L (y, σ) * (gx ell b x (periodicLatticeShift y σ))⁻¹ = 1
  by_cases hσ : σ = 2
  · subst hσ
    have hsh : ((periodicLatticeShift y 2) 2).val = ((y 2).val + 1) % (L 2 + 1) := by
      simp only [periodicLatticeShift, Function.update_self, AdalyFormal.Thin.fin_add_one_val]
    have hNe' : L 2 + 1 = ell * b := hNb 2
    have hsh' : ((periodicLatticeShift y 2) 2).val = ((y 2).val + 1) % (ell * b) := by rw [hsh]; exact congrArg (fun n => ((y 2).val + 1) % n) hNe'
    have hNe : L 2 + 1 = ell * b := hNb 2
    have hv : (y 2).val < ell * b := by rw [← hNe]; exact (y 2).isLt
    have hxv : (x 2).val < ell * b := by rw [← hNe]; exact (x 2).isLt
    have h2 : (y 2).val / b = (x 2).val / b ∨ (y 2).val / b = ((x 2).val + 1) % (ell * b) / b := by
      rw [← hNe]; exact hy 2
    have h2' : ((y 2).val + 1) % (ell * b) / b = (x 2).val / b ∨
        ((y 2).val + 1) % (ell * b) / b = ((x 2).val + 1) % (ell * b) / b := by
      rw [← hNe, ← hsh]; exact hy' 2
    have bn := blk_next (ell := ell) hb hv
    have bq := blk_next (ell := ell) hb hxv
    have hpl : (y 2).val / b < ell := (Nat.div_lt_iff_lt_mul hb).2 hv
    by_cases hseam : (y 2).val = L 2
    · -- seam bond
      have hU : Ustar L (y, 2) = su2NegOne := by simp [Ustar, hseam]
      have hve : (y 2).val + 1 = ell * b := by omega
      have hp : (y 2).val / b = ell - 1 := by
        have h := (AdalyFormal.CoverGeom.cross_cells hb (by omega : 1 ≤ ell)).1
        have e : (y 2).val = ell * b - 1 := by omega
        rw [e]; exact h
      have hp' : ((y 2).val + 1) % (ell * b) / b = 0 := by rw [hve, Nat.mod_self, Nat.zero_div]
      have hq : (x 2).val / b = ell - 1 := by omega
      have e1 : gx ell b x y = 1 := by
        unfold gx; rw [if_neg]; omega
      have e2 : gx ell b x (periodicLatticeShift y 2) = su2NegOne := by
        unfold gx; rw [if_pos]; rw [hsh']; exact ⟨hq, hp'⟩
      rw [hU, e1, e2, su2NegOne_inv, one_mul]; exact su2NegOne_mul_self
    · have hU : Ustar L (y, 2) = 1 := by simp [Ustar, hseam]
      have hne : (y 2).val + 1 ≠ ell * b := by omega
      have hiff : ((x 2).val / b = ell - 1 ∧ (y 2).val / b = 0) ↔
          ((x 2).val / b = ell - 1 ∧ ((y 2).val + 1) % (ell * b) / b = 0) := by omega
      have e1 : gx ell b x (periodicLatticeShift y 2) = gx ell b x y := by
        unfold gx; rw [hsh']; simp only [hiff]
      rw [hU, e1]; simp
  · have hU : Ustar L (y, σ) = 1 := by simp [Ustar, hσ]
    have hs2 : (periodicLatticeShift y σ) 2 = y 2 := by
      simp [periodicLatticeShift, Function.update_of_ne (Ne.symm hσ)]
    have e1 : gx ell b x (periodicLatticeShift y σ) = gx ell b x y := by
      unfold gx; rw [hs2]
    rw [hU, e1]; simp

theorem frobNorm_zero : frobNorm (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]

theorem ddA_zero {L : PeriodicLatticeExtent} (η : ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ddA η (fun _ : Bond L => (0 : Matrix (Fin 2) (Fin 2) ℂ)) x μ = 0 := by
  simp [ddA, curlA]

/-- regularity (with `A = 0`) of the Wilson seam on every `C_x`. -/
theorem regBody_Cx {L : PeriodicLatticeExtent} {ell b M j : ℕ} (hb : 0 < b) (hell : 3 ≤ ell)
    (hNb : ∀ σ : Fin 3, L σ + 1 = ell * b) (x : PeriodicLatticeSite L) {α₀ η : ℝ}
    (hpos : ∀ p : ℕ, 0 < ((10 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p)) :
    RegBodyH ell M 10 (Cx b x) j α₀ η (Ustar L) := by
  refine ⟨gx ell b x, fun _ => 0, fun e he => ?_, fun μ ν y h1 h2 => ?_, fun μ y hy => ?_⟩
  · refine ⟨by simp [HT], ?_, by rw [frobNorm_zero]; simpa using hpos 1⟩
    rw [gauge_bond_trivial hb hell hNb x he]
    simp
  · simp only [sub_self, smul_zero]
    rw [frobNorm_zero]; exact hpos 2
  · rw [ddA_zero, frobNorm_zero]; exact hpos 3

theorem fwd_shift_one {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ∀ σ, (periodicLatticeShift x μ) σ = x σ ∨ (periodicLatticeShift x μ) σ = x σ + 1 := by
  intro σ
  rw [AdalyFormal.M2Coverage.shift_apply]
  split_ifs
  · right; rfl
  · left; rfl

theorem fwd_shift_two {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ ν : Fin 3) (hμν : μ ≠ ν) :
    ∀ σ, (periodicLatticeShift (periodicLatticeShift x μ) ν) σ = x σ ∨
      (periodicLatticeShift (periodicLatticeShift x μ) ν) σ = x σ + 1 := by
  intro σ
  rw [AdalyFormal.M2Coverage.shift_apply, AdalyFormal.M2Coverage.shift_apply]
  by_cases h1 : σ = ν
  · subst h1
    have : σ ≠ μ := fun h => hμν h.symm
    simp [this]
  · by_cases h2 : σ = μ
    · subst h2; simp [hμν]
    · simp [h1, h2]

/-- **strictness of the hypothesis class.**  For `3 ≤ ell ≤ 10`, every `a₀ > 0` with `a₀ ell^(m+1) ≤ 1`, there is a configuration of all
hypotheses of `P428Target8FamilyTorusU` (torus, tower, `Λ`, smallness, a family `F` of unions, `U★`) satisfying the UNION class hypothesis
`ClassCoupledU`, while NO family of triples (with `10 ≤ f`, `f M α₀ ≤ a₀`) satisfies the BOX class hypothesis `ClassCoupledP boxClass` for the same `S, α₀, U★`. -/
theorem strict_hyps (ell m R k : ℕ) (a₀ : ℝ) (hell3 : 3 ≤ ell) (hell10 : ell ≤ 10) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (ha₀ : 0 < a₀) (ha₁ : a₀ * (ell : ℝ) ^ (m + 1) ≤ 1) :
    ∃ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ ∧
      ∃ F : CubeFam (scaleUp ell k Lu),
        (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
        TorusOK ell (ell ^ m) Lu ∧
        ∃ S : Tower (scaleUp ell k Lu), Admissible ell (ell ^ m) R k S ∧
        ∃ Lam : Set (PeriodicLatticeSite Lu), AdalyFormal.StatementLaneG.LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell (ell ^ m) R k S Lam ∧
        ∃ U : LinkCfg (scaleUp ell k Lu),
          ClassCoupledU ell (ell ^ m) F k S α₀ (((ell : ℝ) ^ k)⁻¹) U ∧
          ∀ F' : CubeFam (scaleUp ell k Lu),
            (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F' →
              10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
            ¬ ClassCoupledP boxClass ell (ell ^ m) F' k S α₀ (((ell : ℝ) ^ k)⁻¹) U := by
  have hell0 : 0 < ell := by omega
  have hell2 : 2 ≤ ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 _
  let Lu : PeriodicLatticeExtent := fun _ => ell ^ (m + 1) - 1
  have hLu : ∀ μ : Fin 3, Lu μ + 1 = ell ^ (m + 1) := by
    intro μ; have : 0 < ell ^ (m + 1) := pow_pos hell0 _
    show ell ^ (m + 1) - 1 + 1 = _; omega
  have hT1 : ∀ μ : Fin 3, ell ^ m ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; exact pow_dvd_pow ell (by omega)
  have hT2 : ∀ μ : Fin 3, ell ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; exact dvd_pow_self ell (by omega)
  have hT3 : ∀ μ : Fin 3, ell < Lu μ + 1 := fun μ => by
    rw [hLu μ]
    calc ell = ell ^ 1 := (pow_one ell).symm
      _ < ell ^ (m + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hMr : (0:ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  let α₀ : ℝ := a₀ / (10 * ((ell ^ m : ℕ) : ℝ))
  have hα : 0 < α₀ := by positivity
  have hχ : ∀ e : Bond (scaleUp ell k Lu), |(fun _ => (0:ℝ)) e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10 := fun e => by
    simp only [abs_zero]; positivity
  obtain ⟨hadm, hlam, -⟩ := AdalyFormal.AllC.classHyps_nonvacuous ell (ell ^ m) R k 10 hell0 hM le_rfl Lu hT1 hα hk
    (fun _ => 0) hχ
  have hN : ∀ μ : Fin 3, scaleUp ell k Lu μ + 1 = ell * bigSide (ell ^ m) ell k := by
    intro μ
    have h1 : scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
      unfold scaleUp
      have : 1 ≤ (Lu μ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    rw [h1, hLu μ]; unfold bigSide; ring
  have hb0 : 0 < bigSide (ell ^ m) ell k := Nat.mul_pos hM (pow_pos hell0 k)
  have hBk : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu), x ∈ towerBj (fullTower ell k Lu) k := by
    intro x
    show x ∈ (fullTower ell k Lu).Om k ∧ x ∉ (fullTower ell k Lu).Om (k + 1)
    simp [fullTower]
  have hcu : ∀ x : PeriodicLatticeSite (scaleUp ell k Lu),
      IsClassUnion ell (ell ^ m) k (fullTower ell k Lu) (Cx (bigSide (ell ^ m) ell k) x) k := fun x =>
    isClassUnion_of_unionAt hadm.1
      ⟨le_rfl, blockClosed_Cx _ x, fun y _ => Or.inl (hBk y), ⟨x, mem_Cx_of_forward _ x x (fun σ => Or.inl rfl), hBk x⟩⟩
  let F : CubeFam (scaleUp ell k Lu) := {t | t.2.1 = k ∧ t.2.2 = 10 ∧ ∃ x, t.1 = Cx (bigSide (ell ^ m) ell k) x}
  have hsm : ((10:ℕ):ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = a₀ := by
    simp only [α₀]; push_cast; field_simp
  refine ⟨Lu, α₀, hα, F, ?_, ⟨hT2, hT3, hT1⟩, fullTower ell k Lu, hadm, Set.univ, hlam, Ustar (scaleUp ell k Lu), ?_, ?_⟩
  · intro s j f hmF
    have h1 : f = 10 := hmF.2.1
    subst h1
    exact ⟨le_rfl, le_of_eq hsm⟩
  · refine ⟨fun x hx => ?_, fun p hp' => ?_, fun f sites j hm hu => ?_⟩
    · exact ⟨Cx _ x, k, ⟨10, ⟨rfl, rfl, x, rfl⟩, hcu x⟩, mem_Cx_of_forward _ x x (fun σ => Or.inl rfl)⟩
    · obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
      have hne : μ ≠ ν := ne_of_lt hμν
      refine ⟨Cx _ x, k, ⟨10, ⟨rfl, rfl, x, rfl⟩, hcu x⟩, fun e he => ?_⟩
      rw [AdalyFormal.Thin.edge_mem'] at he
      have f0 : x ∈ Cx (bigSide (ell ^ m) ell k) x := mem_Cx_of_forward _ x x (fun σ => Or.inl rfl)
      have fμ := mem_Cx_of_forward (bigSide (ell ^ m) ell k) x _ (fwd_shift_one x μ)
      have fν := mem_Cx_of_forward (bigSide (ell ^ m) ell k) x _ (fwd_shift_one x ν)
      have fμν := mem_Cx_of_forward (bigSide (ell ^ m) ell k) x _ (fwd_shift_two x μ ν hne)
      have fνμ := mem_Cx_of_forward (bigSide (ell ^ m) ell k) x _ (fwd_shift_two x ν μ hne.symm)
      rcases he with rfl | rfl | rfl | rfl
      · exact ⟨f0, fμ⟩
      · exact ⟨fμ, fμν⟩
      · exact ⟨fν, fνμ⟩
      · exact ⟨f0, fν⟩
    · obtain ⟨hj, hf, x, hs⟩ := hm
      have hj' : j = k := hj
      have hf' : f = 10 := hf
      subst hf' hs
      rw [hj']
      refine regBody_Cx hb0 hell3 hN x (fun p => ?_)
      have : ((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ = 1 := by field_simp
      rw [this]; simp only [one_pow, mul_one]
      push_cast; positivity
  · intro F' hF'
    exact no_box_family ell m k Lu hell2 hell10 hLu ha₁ F' hF'

end UNI.Strict

#print axioms UNI.Strict.hol_gauge
#print axioms UNI.Strict.dist1_hol_le

#print axioms UNI.Strict.strict_hyps
#print axioms UNI.Strict.no_box_family
#print axioms UNI.Strict.regBody_Cx
#print axioms UNI.Strict.gauge_bond_trivial
