import ZGU1N

/-!
# GFC1 -- the flat `G⁻¹ = Δ_a(1)` is NOT `k`-uniformly coercive in the plain fine-lattice `L²` norm.

`GenuineU1.Gen.G1inv_form`:  `⟨x, G₁⁻¹ x⟩ = ‖curl A‖² + ‖R D* A‖² + a ell^k ‖Q_k A‖²`  (flat, full tower).
For the constant-per-direction field `A₀ = constBond c` (`c ≠ 0`):  `curl A₀ = 0`, `R D* A₀ = 0`,
`Q_k A₀ = τ* B_c`  and  `‖A₀‖² = ell^{3k} ‖B_c‖²`  hence

    `⟨A₀, G₁⁻¹ A₀⟩ · ell^{2k} = a · ‖A₀‖²`          (exactly).

So any constant `c_k` with `c_k ‖x‖² ≤ ⟨x, G₁⁻¹ x⟩` on the level-`k` torus satisfies `c_k ≤ a / ell^{2k}`;
for `ell ≥ 2` no `k`-uniform positive constant exists.   Standard axioms only (see `#print axioms`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.FlatCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.GenuineU1H (constBond hodge_converse)

/-- squared `L²` norm of the constant-per-direction bond field: (number of sites) · Σ_μ ‖c_μ‖². -/
theorem norm_sq_constBond (L : PeriodicLatticeExtent) (c : Fin 3 → SuTwo) :
    ‖constBond L c‖ ^ 2 = (∏ μ : Fin 3, ((L μ : ℝ) + 1)) * ∑ μ : Fin 3, ‖c μ‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  show ∑ b : Bond L, ‖c b.2‖ ^ 2 = _
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [show Fintype.card (PeriodicLatticeSite L) = ∏ μ : Fin 3, (L μ + 1) from by
    simp [Fintype.card_pi]]
  push_cast; rfl


section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))
local notation "PP" => PK ell k Lu hell a Lam

/-- the level-`k` fine constant field has `ell^{3k}` times the squared norm of its unit-lattice partner -/
theorem norm_sq_constBond_scaleUp (hell : 0 < ell) (c : Fin 3 → SuTwo) :
    ‖constBond (scaleUp ell k Lu) c‖ ^ 2 = (ell : ℝ) ^ (3 * k) * ‖Bconst Lu c‖ ^ 2 := by
  have hB : Bconst Lu c = constBond Lu c := rfl
  rw [hB, norm_sq_constBond, norm_sq_constBond]
  have hpos : ∀ μ : Fin 3, 1 ≤ (Lu μ + 1) * ell ^ k := fun μ =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) (pow_pos hell k).ne')
  have hprod : (∏ μ : Fin 3, (((scaleUp ell k Lu μ : ℕ) : ℝ) + 1))
      = (ell : ℝ) ^ (3 * k) * ∏ μ : Fin 3, ((Lu μ : ℝ) + 1) := by
    have h1 : ∀ μ : Fin 3, (((scaleUp ell k Lu μ : ℕ) : ℝ) + 1) = (ell : ℝ) ^ k * ((Lu μ : ℝ) + 1) := by
      intro μ
      have : scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
        unfold scaleUp; exact Nat.sub_add_cancel (hpos μ)
      have h2 : (((scaleUp ell k Lu μ + 1 : ℕ)) : ℝ) = (((Lu μ + 1) * ell ^ k : ℕ) : ℝ) := by rw [this]
      push_cast at h2
      linarith [h2]
    rw [Finset.prod_congr rfl (fun μ _ => h1 μ), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm k 3]
  rw [hprod]; ring

/-- the quadratic form of `G₁⁻¹` on the constant-per-direction fine field is `a ell^k ‖B_c‖²` -/
theorem constMode_form (hN : ∀ μ, 1 ≤ Lu μ) (c : Fin 3 → SuTwo) :
    ⟪(⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩ : ↥(bondSupp (PP).G)),
      (PP).G1inv ⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩⟫
      = a * (ell : ℝ) ^ k * ‖Bconst Lu c‖ ^ 2 := by
  have hFS : (PP).FullSupp := PK_fullSupp ell k Lu hell a Lam
  set A0 : ↥(bondSupp (PP).G) := ⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩ with hA0
  have hQ0 : (PP).data.Q A0 = ContinuousLinearMap.adjoint (PP).tau (Bconst Lu c) :=
    constMode_Q ell k Lu hell a Lam hN c
  have hnormy : ‖ContinuousLinearMap.adjoint (PP).tau (Bconst Lu c)‖ = ‖Bconst Lu c‖ :=
    Gen.tau_adj_norm (PP) hFS _
  rw [Gen.G1inv_form (PP) hFS (PK_Om0_univ ell k Lu hell a Lam) rfl]
  obtain ⟨hc1, hc2, -⟩ := hodge_converse (L := scaleUp ell k Lu) c 0
  have e1 : curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G A0) = 0 := hc1
  have e2 : Tfull (PP).G (PP).U (iE (PP).G A0) = 0 := by
    show (Rproj (PP).G flatCfg) (gradAdj flatCfg (iE (PP).G A0)) = 0
    rw [show gradAdj flatCfg (iE (PP).G A0) = 0 from hc2, map_zero]
  show ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell k Lu)) (iE (PP).G A0)‖ ^ 2 +
    ‖Tfull (PP).G (PP).U (iE (PP).G A0)‖ ^ 2 + a * (ell : ℝ) ^ k * ‖(PP).data.Q A0‖ ^ 2 = _
  rw [e1, e2, hQ0, hnormy]; simp

/-- **EXACT**: `⟨A₀, G₁⁻¹ A₀⟩ · ell^{2k} = a · ‖A₀‖²` for the constant-per-direction fine field. -/
theorem flat_Ginv_const_mode (hN : ∀ μ, 1 ≤ Lu μ) (c : Fin 3 → SuTwo) :
    ⟪(⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩ : ↥(bondSupp (PP).G)),
      (PP).G1inv ⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩⟫ * (ell : ℝ) ^ (2 * k)
      = a * ‖(⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩ : ↥(bondSupp (PP).G))‖ ^ 2 := by
  rw [constMode_form ell k Lu hell a Lam hN c]
  have hn : ‖(⟨constBond (scaleUp ell k Lu) c, bondSupp_G ell k Lu _⟩ : ↥(bondSupp (PP).G))‖ ^ 2
      = (ell : ℝ) ^ (3 * k) * ‖Bconst Lu c‖ ^ 2 := norm_sq_constBond_scaleUp ell k Lu hell c
  rw [hn]
  have : (ell : ℝ) ^ (3 * k) = (ell : ℝ) ^ k * (ell : ℝ) ^ (2 * k) := by rw [← pow_add]; congr 1; ring
  rw [this]; ring

end

/-- the constant-per-direction witness is nonzero (for `X ≠ 0`, constant `X` in every direction) -/
theorem constBond_ne_zero (L : PeriodicLatticeExtent) (X : SuTwo) (hX : X ≠ 0) :
    constBond L (fun _ => X) ≠ 0 := by
  intro h
  have h2 : ‖constBond L (fun _ : Fin 3 => X)‖ ^ 2 = 0 := by rw [h]; simp
  rw [norm_sq_constBond] at h2
  have hp : 0 < ∏ μ : Fin 3, ((L μ : ℝ) + 1) := Finset.prod_pos (fun μ _ => by positivity)
  have hs : 0 < ∑ μ : Fin 3, ‖(fun _ : Fin 3 => X) μ‖ ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : 0 < ‖X‖ := norm_pos_iff.mpr hX
    positivity
  have := mul_pos hp hs
  linarith

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))
local notation "PP" => PK ell k Lu hell a Lam

/-- **UPPER BOUND ON ANY COERCIVITY CONSTANT** at level `k`: `c ≤ a / ell^{2k}` (flat, full tower). -/
theorem coercivity_constant_le (hN : ∀ μ, 1 ≤ Lu μ) (c : ℝ)
    (hc : ∀ x : ↥(bondSupp (PP).G), c * ‖x‖ ^ 2 ≤ ⟪x, (PP).G1inv x⟫) :
    c * (ell : ℝ) ^ (2 * k) ≤ a := by
  obtain ⟨X, hX⟩ := exists_ne_zero_suTwo
  set x : ↥(bondSupp (PP).G) := ⟨constBond (scaleUp ell k Lu) (fun _ => X), bondSupp_G ell k Lu _⟩ with hx
  have hx0 : 0 < ‖x‖ ^ 2 := by
    have : x ≠ 0 := fun h => constBond_ne_zero (scaleUp ell k Lu) X hX (congrArg Subtype.val h)
    have := norm_pos_iff.mpr this
    positivity
  have h1 := flat_Ginv_const_mode ell k Lu hell a Lam hN (fun _ => X)
  have h2 := hc x
  have hp : (0 : ℝ) < (ell : ℝ) ^ (2 * k) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  have h3 : c * ‖x‖ ^ 2 * (ell : ℝ) ^ (2 * k) ≤ a * ‖x‖ ^ 2 := by
    calc c * ‖x‖ ^ 2 * (ell : ℝ) ^ (2 * k) ≤ ⟪x, (PP).G1inv x⟫ * (ell : ℝ) ^ (2 * k) :=
          mul_le_mul_of_nonneg_right h2 hp.le
      _ = a * ‖x‖ ^ 2 := h1
  nlinarith [h3, hx0]

end

#print axioms norm_sq_constBond
#print axioms norm_sq_constBond_scaleUp
#print axioms constMode_form
#print axioms flat_Ginv_const_mode

/-- **NO `k`-UNIFORM COERCIVITY** (flat `Δ_a(1)`, plain fine-lattice `L²` norm, `ell ≥ 2`, any `a > 0`,
any admissible unit torus `Lu`): for every `c > 0` there is a level `k` and a nonzero field `x` with
`⟨x, G₁⁻¹ x⟩ < c ‖x‖²`. -/
theorem no_k_uniform_coercivity (ell : ℕ) (hell2 : 2 ≤ ell) (a : ℝ) (ha : 0 < a)
    (Lu : PeriodicLatticeExtent) (hN : ∀ μ, 1 ≤ Lu μ) (c : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, ∃ x : ↥(bondSupp (PK ell k Lu (by omega) a Set.univ).G), x ≠ 0 ∧
      ⟪x, (PK ell k Lu (by omega) a Set.univ).G1inv x⟫ < c * ‖x‖ ^ 2 := by
  obtain ⟨X, hX⟩ := exists_ne_zero_suTwo
  have hell1 : (1 : ℝ) < ell := by exact_mod_cast hell2
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (a / c) hell1
  have hell0 : 0 < ell := by omega
  refine ⟨m, ⟨constBond (scaleUp ell m Lu) (fun _ => X), bondSupp_G ell m Lu _⟩, ?_, ?_⟩
  · intro h; exact constBond_ne_zero (scaleUp ell m Lu) X hX (congrArg Subtype.val h)
  · set x : ↥(bondSupp (PK ell m Lu hell0 a Set.univ).G) :=
      ⟨constBond (scaleUp ell m Lu) (fun _ => X), bondSupp_G ell m Lu _⟩ with hx
    have hx0 : 0 < ‖x‖ ^ 2 := by
      have : x ≠ 0 := fun h => constBond_ne_zero (scaleUp ell m Lu) X hX (congrArg Subtype.val h)
      have := norm_pos_iff.mpr this
      positivity
    have h1 := flat_Ginv_const_mode ell m Lu hell0 a Set.univ hN (fun _ => X)
    have hp : (0 : ℝ) < (ell : ℝ) ^ (2 * m) := by positivity
    have hle : (ell : ℝ) ^ m ≤ (ell : ℝ) ^ (2 * m) :=
      pow_le_pow_right₀ hell1.le (by omega)
    have hm' : a < c * (ell : ℝ) ^ (2 * m) := by
      have : a / c < (ell : ℝ) ^ (2 * m) := lt_of_lt_of_le hm hle
      rw [div_lt_iff₀ hc] at this; linarith
    by_contra hcon
    push_neg at hcon
    have : c * ‖x‖ ^ 2 * (ell : ℝ) ^ (2 * m) ≤ a * ‖x‖ ^ 2 := by
      calc c * ‖x‖ ^ 2 * (ell : ℝ) ^ (2 * m)
          ≤ ⟪x, (PK ell m Lu hell0 a Set.univ).G1inv x⟫ * (ell : ℝ) ^ (2 * m) :=
            mul_le_mul_of_nonneg_right hcon hp.le
        _ = a * ‖x‖ ^ 2 := h1
    nlinarith [hx0]

#print axioms constBond_ne_zero
#print axioms coercivity_constant_le
#print axioms no_k_uniform_coercivity

end AdalyFormal.FlatCoercivity
