import W6F

/-!
# W6H -- the weighted energy of the multi-level bond right inverse, and a right inverse of `Q_U` with that energy
(the W6 input of PLAN D2) (W6 lane, 2026-10-13)

Norms: `‖y‖_D² = Σ_p ℓ^{lev p} ‖y_p‖²` (`nD`) on `L²(𝔅)`; on bonds the stratum-weighted `‖x‖_w² = Σ_b ℓ^{-2 bstrat b}‖x_b‖²`
(lane B's `AdalyFormal.M1.wnormSq`, the norm of lane E's W4) and the shift-gradient `gradW x ν = Σ_b ‖x(b + e_ν) − x(b)‖²`
(the same formula as DL46 `gradE`).
* `E_wnorm` : `‖E y‖_w² ≤ ℓ² CE ‖y‖_D²`;  `E_grad` : `gradW (E y) ν ≤ 2 GE ‖y‖_D²` (smooth profiles: the kernels are continuous at
  the block scale; `GE = 2(419904 + 4665600)`).
* `flat_D`, `drift_D` : `‖Q₁ x‖_D² ≤ 3ℓ² ‖x‖_w²`, `‖(Q_U − Q₁) x‖_D² ≤ 3ℓ² δ² ‖x‖_w²`.
* `Eright_wnorm`, `Eright_grad` : the same for `E' = E(2 − K)` with `CwE = ℓ² CE (8 + 6ℓ⁴ CE)`, `CgE = 2 GE (8 + 6ℓ⁴ CE)`.
* **`bond_rightinv_strat`** : under the hypotheses of `qs_injective_strat` and `3ℓ²δ² CwE ≤ 1/4`: for every `u ∈ L²(𝔅)` there
  is `x ∈ E₀` with `Q_U x = u`, `‖x‖_w² ≤ 4 CwE ‖u‖_D²` and `gradW x ν ≤ 4 CgE ‖u‖_D²` for every direction `ν`.
All constants depend on `ℓ` only (not on `k`, `M`, `R`, the volume, the tower).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace AdalyFormal.W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.DLayer (Foot bondRestr)
open AdalyFormal.BondComposite (TowerClass)
open AdalyFormal.W6P (gbondE tprof pprof SProf sprof_tprof sprof_pprof gbondE_grad_sq sbondE_grad_sq)

/-- the shift-gradient energy in direction `ν` (DL46 `gradE`) -/
noncomputable def gradW {L : PeriodicLatticeExtent} (x : BondFnL2 L) (ν : Fin 3) : ℝ :=
  ∑ b : Bond L, ‖x (periodicLatticeShift b.1 ν, b.2) - x b‖ ^ 2

/-- `‖Σ_{i} v_i‖² ≤ 2 Σ ‖v_i‖²` when at most two terms are nonzero -/
theorem norm_sq_sum_two {ι V : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] (v : ι → V) (a b : ι)
    (h : ∀ i, v i ≠ 0 → i = a ∨ i = b) : ‖∑ i, v i‖ ^ 2 ≤ 2 * ∑ i, ‖v i‖ ^ 2 := by
  have hsum : ∑ i, v i = ∑ i ∈ ({a, b} : Finset ι), v i := by
    rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset ι))]
    intro i _ hi
    by_contra hne
    rcases h i hne with h1 | h1
    · exact hi (by rw [h1]; simp)
    · exact hi (by rw [h1]; simp)
  have hcard : (({a, b} : Finset ι)).card ≤ 2 := Finset.card_le_two
  have h1 : ‖∑ i ∈ ({a, b} : Finset ι), v i‖ ≤ ∑ i ∈ ({a, b} : Finset ι), ‖v i‖ := norm_sum_le _ _
  have h2 : (∑ i ∈ ({a, b} : Finset ι), ‖v i‖) ^ 2 ≤ (({a, b} : Finset ι)).card * ∑ i ∈ ({a, b} : Finset ι), ‖v i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ i ∈ ({a, b} : Finset ι), ‖v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have h0 : 0 ≤ ∑ i ∈ ({a, b} : Finset ι), ‖v i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [hsum]
  calc ‖∑ i ∈ ({a, b} : Finset ι), v i‖ ^ 2 ≤ (∑ i ∈ ({a, b} : Finset ι), ‖v i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (({a, b} : Finset ι)).card * ∑ i ∈ ({a, b} : Finset ι), ‖v i‖ ^ 2 := h2
    _ ≤ 2 * ∑ i ∈ ({a, b} : Finset ι), ‖v i‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ h0; exact_mod_cast hcard
    _ ≤ 2 * ∑ i, ‖v i‖ ^ 2 := by linarith

/-- the gradient constant of the upper kernel -/
theorem uprof_grad (n : ℕ) (hn2 : 2 ≤ n) {L : PeriodicLatticeExtent} (hdvd : ∀ ν, n ∣ L ν + 1) (ν0 : Fin 3)
    (W : CoarseBond L n → SuTwo) :
    ∑ b : Bond L, ‖gbondE (AdalyFormal.W6.uprof n) (pprof n) n W (periodicLatticeShift b.1 ν0, b.2)
        - gbondE (AdalyFormal.W6.uprof n) (pprof n) n W b‖ ^ 2
      ≤ 4665600 * n * ∑ c : CoarseBond L n, ‖W c‖ ^ 2 := by
  refine gbondE_grad_sq (AdalyFormal.W6.sprof_uprof n hn2) (sprof_pprof n (by omega)) hdvd ν0 4665600 (fun μ => ?_) W
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  rw [Finset.prod_pow]
  have hall : ∏ ν : Fin 3, (if ν = μ then (33 : ℝ) else 3 / 2) = 297 / 4 := by
    rw [Fin.prod_univ_three]; fin_cases μ <;> simp <;> norm_num
  have hsplit : ∏ ν : Fin 3, (if ν = μ then (33 : ℝ) else 3 / 2)
      = (if ν0 = μ then (33 : ℝ) else 3 / 2) * ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then (33 : ℝ) else 3 / 2) :=
    Fintype.prod_eq_mul_prod_compl ν0 _
  rw [hall] at hsplit
  by_cases h : ν0 = μ
  · rw [if_pos h] at hsplit
    have hP : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then (33 : ℝ) else 3 / 2) = 9 / 4 := by linarith
    rw [if_pos h, hP]; nlinarith
  · rw [if_neg h] at hsplit
    have hP : ∏ ν ∈ ({ν0}ᶜ : Finset (Fin 3)), (if ν = μ then (33 : ℝ) else 3 / 2) = 99 / 2 := by linarith
    rw [if_neg h, hP]; nlinarith

section energy
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- the `D` weight `ℓ^{lev p}` -/
noncomputable def wD (p : BIdx (geomOf ell k S)) : ℝ := (ell : ℝ) ^ (p.1 : ℕ)

theorem wD_pos (hell : 0 < ell) (p : BIdx (geomOf ell k S)) : 0 < wD p := by
  unfold wD; have : (0 : ℝ) < ell := by exact_mod_cast hell
  positivity

/-- `‖y‖_D²` -/
noncomputable def nD (y : FSp (geomOf ell k S)) : ℝ := ∑ p, wD p * ‖y p‖ ^ 2

theorem nD_nonneg (hell : 0 < ell) (y : FSp (geomOf ell k S)) : 0 ≤ nD y :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (wD_pos hell p).le (sq_nonneg _))

/-- the gradient constant of `E` -/
noncomputable def GE : ℝ := 2 * (419904 + 4665600)

/-- one level, gradient -/
theorem Elev_grad (hell : 0 < ell) (hell2 : 2 ≤ ell) (y : FSp (geomOf ell k S)) (j : Fin (k + 1)) (ν0 : Fin 3) :
    ∑ b, ‖Elev hell j y (periodicLatticeShift b.1 ν0, b.2) - Elev hell j y b‖ ^ 2
      ≤ GE * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          wD (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖y ⟨j, r⟩‖ ^ 2 := by
  have hn : 0 < ell ^ (j : ℕ) := pow_pos hell _
  have hdv : ∀ ν, ell ^ (j : ℕ) ∣ scaleUp ell k Lu ν + 1 :=
    fun ν => AdalyFormal.BondComposite.hdvd_scaleUp ell k Lu hell _ (Nat.lt_succ_iff.mp j.isLt) ν
  set n : ℝ := ((ell ^ (j : ℕ) : ℕ) : ℝ) with hndef
  have hwD : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      wD (⟨j, r⟩ : BIdx (geomOf ell k S)) = n := by
    intro r; unfold wD; rw [hndef]; push_cast; rfl
  simp only [hwD]
  rw [← Finset.mul_sum]
  set lo := gbondE (tprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) (Wlo hell j y) with hlo
  set up := gbondE (AdalyFormal.W6.uprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) (Wup hell j y) with hup
  have hsplit : ∀ b : Bond (scaleUp ell k Lu),
      ‖Elev hell j y (periodicLatticeShift b.1 ν0, b.2) - Elev hell j y b‖ ^ 2
        ≤ 2 * ‖lo (periodicLatticeShift b.1 ν0, b.2) - lo b‖ ^ 2 + 2 * ‖up (periodicLatticeShift b.1 ν0, b.2) - up b‖ ^ 2 := by
    intro b
    rw [Elev_eq, Elev_eq]
    have e : lo (periodicLatticeShift b.1 ν0, b.2) + up (periodicLatticeShift b.1 ν0, b.2) - (lo b + up b)
        = (lo (periodicLatticeShift b.1 ν0, b.2) - lo b) + (up (periodicLatticeShift b.1 ν0, b.2) - up b) := by abel
    rw [e]
    exact norm_add_sq_le2 _ _
  have hglo : ∑ b : Bond (scaleUp ell k Lu), ‖lo (periodicLatticeShift b.1 ν0, b.2) - lo b‖ ^ 2
      ≤ 419904 * n * ∑ c, ‖Wlo hell j y c‖ ^ 2 := sbondE_grad_sq _ hn hdv ν0 (Wlo hell j y)
  have hgup : ∑ b : Bond (scaleUp ell k Lu), ‖up (periodicLatticeShift b.1 ν0, b.2) - up b‖ ^ 2
      ≤ 4665600 * n * ∑ c, ‖Wup hell j y c‖ ^ 2 := by
    by_cases hj0 : (j : ℕ) = 0
    · have hW : ∀ c, Wup hell j y c = 0 := by
        intro c
        unfold Wup
        refine Finset.sum_eq_zero (fun r _ => ?_)
        unfold Fup
        rw [if_neg]
        rintro ⟨hu, -⟩
        have := hu.1
        simp only at this
        omega
      have h0 : ∀ b, up b = 0 := by
        intro b; rw [hup]; unfold gbondE; simp [hW]
      simp only [h0, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, hW]
      simp
    · have hn2 : 2 ≤ ell ^ (j : ℕ) := le_trans hell2 (by
        calc ell = ell ^ 1 := (pow_one ell).symm
          _ ≤ ell ^ (j : ℕ) := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hj0))
      exact uprof_grad _ hn2 hdv ν0 (Wup hell j y)
  have hmass := W_mass hell j y
  have hA : 0 ≤ ∑ c, ‖Wlo hell j y c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ ∑ c, ‖Wup hell j y c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn0 : 0 ≤ n := by positivity
  unfold GE
  calc ∑ b, ‖Elev hell j y (periodicLatticeShift b.1 ν0, b.2) - Elev hell j y b‖ ^ 2
      ≤ ∑ b : Bond (scaleUp ell k Lu), (2 * ‖lo (periodicLatticeShift b.1 ν0, b.2) - lo b‖ ^ 2
          + 2 * ‖up (periodicLatticeShift b.1 ν0, b.2) - up b‖ ^ 2) := Finset.sum_le_sum (fun b _ => hsplit b)
    _ = 2 * ∑ b : Bond (scaleUp ell k Lu), ‖lo (periodicLatticeShift b.1 ν0, b.2) - lo b‖ ^ 2
          + 2 * ∑ b : Bond (scaleUp ell k Lu), ‖up (periodicLatticeShift b.1 ν0, b.2) - up b‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (419904 * n * ∑ c, ‖Wlo hell j y c‖ ^ 2) + 2 * (4665600 * n * ∑ c, ‖Wup hell j y c‖ ^ 2) := by
        linarith
    _ ≤ 2 * (419904 + 4665600) * (n * (∑ c, ‖Wlo hell j y c‖ ^ 2 + ∑ c, ‖Wup hell j y c‖ ^ 2)) :=
        comb_le _ _ _ _ _ (by norm_num) (by norm_num) hA hB hn0
    _ = 2 * (419904 + 4665600) * (n * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          ‖y ⟨j, r⟩‖ ^ 2) := by rw [hmass]

/-- the level part vanishes off its stratum -/
theorem Elev_diff_two (hell : 0 < ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S))
    (b : Bond (scaleUp ell k Lu)) (ν0 : Fin 3) (i : Fin (k + 1))
    (hi : Elev hell i y (periodicLatticeShift b.1 ν0, b.2) - Elev hell i y b ≠ 0) :
    i = ⟨AdalyFormal.M1.strat S k (periodicLatticeShift b.1 ν0), Nat.lt_succ_of_le (AdalyFormal.M1.strat_le S k _)⟩
      ∨ i = ⟨AdalyFormal.M1.strat S k b.1, Nat.lt_succ_of_le (AdalyFormal.M1.strat_le S k _)⟩ := by
  by_cases h1 : Elev hell i y (periodicLatticeShift b.1 ν0, b.2) = 0
  · right
    have h2 : Elev hell i y b ≠ 0 := by intro h2; apply hi; rw [h1, h2, sub_self]
    exact Fin.ext (Elev_lev hell hS y b i h2).symm
  · left
    exact Fin.ext (Elev_lev hell hS y _ i h1).symm

/-- **gradient of `E`** -/
theorem E_grad (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S)) (ν0 : Fin 3) :
    gradW (EflatL hell y) ν0 ≤ 2 * GE * nD y := by
  classical
  unfold gradW
  have hpt : ∀ b : Bond (scaleUp ell k Lu),
      ‖(EflatL hell y) (periodicLatticeShift b.1 ν0, b.2) - (EflatL hell y) b‖ ^ 2
        ≤ 2 * ∑ j : Fin (k + 1), ‖Elev hell j y (periodicLatticeShift b.1 ν0, b.2) - Elev hell j y b‖ ^ 2 := by
    intro b
    rw [EflatL_eq_sum, EflatL_eq_sum, ← Finset.sum_sub_distrib]
    exact norm_sq_sum_two _ _ _ (fun i hi => Elev_diff_two hell hS y b ν0 i hi)
  refine (Finset.sum_le_sum (fun b _ => hpt b)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  unfold nD
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wD p * ‖y p‖ ^ 2), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have h := Elev_grad hell hell2 y j ν0
  exact le_of_le_of_eq (mul_le_mul_of_nonneg_left h (by norm_num)) (by ring)

/-- `ℓ^{-2 bstrat b} ≤ ℓ² ℓ^{-2 strat b.1}` -/
theorem wt_bstrat_le (hell : 0 < ell) (hS : Admissible ell M R k S) (hR1 : 1 ≤ R) (hM : 1 ≤ M)
    (b : Bond (scaleUp ell k Lu)) :
    (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2
      ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1)⁻¹) ^ 2 := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hge := AdalyFormal.M1.bstrat_ge hS hR1 hM hell b
  have hp : (ell : ℝ) ^ AdalyFormal.M1.strat S k b.1 ≤ (ell : ℝ) ^ (AdalyFormal.M1.bstrat S k b + 1) :=
    pow_le_pow_right₀ hellR hge
  have hpos : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.strat S k b.1 := by positivity
  have hpos' : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.bstrat S k b := by positivity
  have h2 : ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2
      ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b) ^ 2 := by
    calc ((ell : ℝ) ^ AdalyFormal.M1.strat S k b.1) ^ 2 ≤ ((ell : ℝ) ^ (AdalyFormal.M1.bstrat S k b + 1)) ^ 2 :=
          pow_le_pow_left₀ hpos.le hp 2
      _ = (ell : ℝ) ^ 2 * ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b) ^ 2 := by ring
  rw [inv_pow, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  linarith

/-- **`‖E y‖_w² ≤ ℓ² CE ‖y‖_D²`** -/
theorem E_wnorm (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hR1 : 1 ≤ R) (hM : 1 ≤ M)
    (y : FSp (geomOf ell k S)) :
    AdalyFormal.M1.wnormSq S ell k (EflatL hell y) ≤ (ell : ℝ) ^ 2 * CE * nD y := by
  unfold AdalyFormal.M1.wnormSq
  have hpt : ∀ b : Bond (scaleUp ell k Lu),
      (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 * ‖(WithLp.ofLp (EflatL hell y)) b‖ ^ 2
        ≤ (ell : ℝ) ^ 2 * ∑ j : Fin (k + 1), (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖Elev hell j y b‖ ^ 2 := by
    intro b
    have h1 : ‖(WithLp.ofLp (EflatL hell y)) b‖ ^ 2 = ∑ j : Fin (k + 1), ‖Elev hell j y b‖ ^ 2 := EflatL_pt hell hS y b
    rw [h1, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hj : Elev hell j y b = 0
    · rw [hj, norm_zero]; simp
    · have hs := Elev_lev hell hS y b j hj
      have hw := wt_bstrat_le hell hS hR1 hM b
      rw [hs] at hw
      have := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖Elev hell j y b‖)
      linarith
  refine (Finset.sum_le_sum (fun b _ => hpt b)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  unfold nD
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wD p * ‖y p‖ ^ 2), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hn : (0 : ℝ) < (ell : ℝ) ^ (j : ℕ) := by positivity
  have h := Elev_norm_sq hell hell2 y j
  set X := ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
    wD (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖y ⟨j, r⟩‖ ^ 2 with hX
  have e2 : ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      wF (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖y ⟨j, r⟩‖ ^ 2 = ((ell : ℝ) ^ (j : ℕ)) ^ 2 * X := by
    rw [hX, Finset.mul_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); unfold wF wD; ring
  rw [e2] at h
  have e1 : ∑ b, (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖Elev hell j y b‖ ^ 2
      = (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ b, ‖Elev hell j y b‖ ^ 2 := by rw [Finset.mul_sum]
  have hinv : (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((ell : ℝ) ^ (j : ℕ)) ^ 2 = 1 := by field_simp
  have key : (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ b, ‖Elev hell j y b‖ ^ 2 ≤ CE * X := by
    calc (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ b, ‖Elev hell j y b‖ ^ 2
        ≤ (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * (CE * (((ell : ℝ) ^ (j : ℕ)) ^ 2 * X)) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = CE * X * ((((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((ell : ℝ) ^ (j : ℕ)) ^ 2) := by ring
      _ = CE * X := by rw [hinv, mul_one]
  rw [e1]
  exact le_of_le_of_eq (mul_le_mul_of_nonneg_left key (by positivity)) (by rw [hX]; ring)

open Classical in
/-- level footprints in the `w` weight: `Σ_j ℓ^{-2j} ‖x|_{F_j}‖² ≤ 3ℓ² ‖x‖_w²` -/
theorem foot_levels_w (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ j : Fin (k + 1), (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2
      ≤ 3 * (ell : ℝ) ^ 2 * AdalyFormal.M1.wnormSq S ell k x := by
  have hell : 0 < ell := by omega
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  simp only [bondRestr_norm_sq, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold AdalyFormal.M1.wnormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  set s := AdalyFormal.M1.strat S k e.1
  have hle : ∀ j : Fin (k + 1), (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * (if FootL (S := S) j e then ‖x e‖ ^ 2 else 0)
      ≤ (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0)
        * ((ell : ℝ) ^ 2 * ((((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e)⁻¹) ^ 2 * ‖x e‖ ^ 2)) := by
    intro j
    by_cases hF : FootL (S := S) j e
    · obtain ⟨r, hr⟩ := hF
      have hw := AdalyFormal.M1IMS.row_window (κ := 1) (c := 5) hS Nat.one_pos hM hell2 (by omega) (by omega)
        le_rfl (⟨j, r⟩ : BIdx (geomOf ell k S)) e hr
      rw [if_pos ⟨r, hr⟩, if_pos hw, one_mul]
      have hbs : AdalyFormal.M1.bstrat S k e ≤ s := min_le_left _ _
      have hsj : s ≤ (j : ℕ) + 1 := hw.1
      -- ℓ^{-2j} ≤ ℓ² ℓ^{-2 bstrat}
      have hp : (ell : ℝ) ^ AdalyFormal.M1.bstrat S k e ≤ (ell : ℝ) ^ ((j : ℕ) + 1) :=
        pow_le_pow_right₀ hellR (by omega)
      have hpos : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.bstrat S k e := by positivity
      have hpos' : (0 : ℝ) < (ell : ℝ) ^ (j : ℕ) := by positivity
      have hkey : (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e)⁻¹) ^ 2 := by
        have h2 : ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e) ^ 2 ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (j : ℕ)) ^ 2 := by
          calc ((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e) ^ 2 ≤ ((ell : ℝ) ^ ((j : ℕ) + 1)) ^ 2 :=
                pow_le_pow_left₀ hpos.le hp 2
            _ = (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (j : ℕ)) ^ 2 := by ring
        rw [inv_pow, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        linarith
      have := mul_le_mul_of_nonneg_right hkey (sq_nonneg ‖x e‖)
      linarith
    · rw [if_neg hF, mul_zero]; split_ifs <;> positivity
  refine (Finset.sum_le_sum (fun j _ => hle j)).trans ?_
  rw [← Finset.sum_mul]
  have h3 := AdalyFormal.M1IMS.levels_le_three k s
  have hnn : 0 ≤ (ell : ℝ) ^ 2 * ((((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e)⁻¹) ^ 2 * ‖x e‖ ^ 2) := by positivity
  calc (∑ j : Fin (k + 1), (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0))
        * ((ell : ℝ) ^ 2 * ((((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e)⁻¹) ^ 2 * ‖x e‖ ^ 2))
      ≤ 3 * ((ell : ℝ) ^ 2 * ((((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e)⁻¹) ^ 2 * ‖x e‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right h3 hnn
    _ = 3 * (ell : ℝ) ^ 2 * ((((ell : ℝ) ^ AdalyFormal.M1.bstrat S k e)⁻¹) ^ 2 * ‖(WithLp.ofLp x) e‖ ^ 2) := by ring

/-- `ℓ^j · ‖·‖² = ℓ^{-2j} · (ℓ^{3j} ‖·‖²)` -/
theorem wD_eq (hell : 0 < ell) (p : BIdx (geomOf ell k S)) : wD p = (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 * wF p := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hx : (0 : ℝ) < (ell : ℝ) ^ (p.1 : ℕ) := pow_pos hellR _
  unfold wD wF
  field_simp <;> ring

/-- **`‖(Q_U − Q₁) x‖_D² ≤ 3ℓ² δ² ‖x‖_w²`** -/
theorem drift_D (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (V : AdalyFormal.IngredientFamilyR2.Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) V) k) (hcl : TowerClass ell k Lu V ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wD p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
      ≤ 3 * (ell : ℝ) ^ 2 * delW ell k ε ^ 2 * AdalyFormal.M1.wnormSq S ell k x := by
  have hell : 0 < ell := by omega
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wD p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p
      - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2)]
  have hlev : ∀ j : Fin (k + 1), ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      wD (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ delW ell k ε ^ 2 * ((((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2) := by
    intro j
    have h := level_drift (S := S) hell V ε hreg hcl hε0 hsm j x
    simp only [wD_eq hell]
    have e : ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (((ell : ℝ) ^ ((⟨j, r⟩ : BIdx (geomOf ell k S)).1 : ℕ))⁻¹) ^ 2 * wF (⟨j, r⟩ : BIdx (geomOf ell k S))
          * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩ - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
        = (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
            - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); unfold wF; ring
    rw [e]
    have hI : 0 ≤ (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 := sq_nonneg _
    calc (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
            - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
        ≤ (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * (delW ell k ε ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h hI
      _ = _ := by ring
  refine (Finset.sum_le_sum (fun j _ => hlev j)).trans ?_
  rw [← Finset.mul_sum]
  have h3 := foot_levels_w hell2 hS hM hR x
  have hd : 0 ≤ delW ell k ε ^ 2 := sq_nonneg _
  calc delW ell k ε ^ 2 * ∑ j : Fin (k + 1), (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2
      ≤ delW ell k ε ^ 2 * (3 * (ell : ℝ) ^ 2 * AdalyFormal.M1.wnormSq S ell k x) := mul_le_mul_of_nonneg_left h3 hd
    _ = _ := by ring

/-- **`‖Q₁ x‖_D² ≤ 3ℓ² ‖x‖_w²`** -/
theorem flat_D (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wD p * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
      ≤ 3 * (ell : ℝ) ^ 2 * AdalyFormal.M1.wnormSq S ell k x := by
  have hell : 0 < ell := by omega
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wD p * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2)]
  have hlev : ∀ j : Fin (k + 1), ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      wD (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by
    intro j
    have h := level_size (S := S) hell (trivialU _) (fun _ => 0) (regTower_triv hell) (towerClass_triv hell)
      (fun _ _ => le_rfl) (fun _ _ => rhoOf_zero_lt ell) j x
    rw [expW_zero hell, one_pow, one_mul] at h
    simp only [wD_eq hell]
    have e : ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (((ell : ℝ) ^ ((⟨j, r⟩ : BIdx (geomOf ell k S)).1 : ℕ))⁻¹) ^ 2 * wF (⟨j, r⟩ : BIdx (geomOf ell k S))
          * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
        = (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); unfold wF; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
  refine (Finset.sum_le_sum (fun j _ => hlev j)).trans ?_
  exact foot_levels_w hell2 hS hM hR x

theorem nD_sub_le (hell : 0 < ell) (y z : FSp (geomOf ell k S)) : nD (y - z) ≤ 2 * nD y + 2 * nD z := by
  unfold nD
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have hw := (wD_pos hell p).le
  have h2 : ‖(y - z) p‖ ^ 2 ≤ 2 * ‖y p‖ ^ 2 + 2 * ‖z p‖ ^ 2 := by
    rw [show (y - z) p = y p + (-(z p)) by rw [sub_eq_add_neg]; rfl]
    have := norm_add_sq_le2 (y p) (-(z p))
    rwa [norm_neg] at this
  nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem nD_add_le (hell : 0 < ell) (y z : FSp (geomOf ell k S)) : nD (y + z) ≤ 2 * nD y + 2 * nD z := by
  have := nD_sub_le hell y (-z)
  rw [sub_neg_eq_add] at this
  have hz : nD (-z) = nD z := by
    unfold nD; refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [show (-z) p = -(z p) from rfl, norm_neg]
  rw [hz] at this; exact this

theorem nD_smul (c : ℝ) (y : FSp (geomOf ell k S)) : nD (c • y) = c ^ 2 * nD y := by
  unfold nD
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show (c • y) p = c • y p from rfl, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- the `w`-norm constant of `E'` -/
noncomputable def CwE (ell : ℕ) : ℝ := (ell : ℝ) ^ 2 * CE * (8 + 6 * (ell : ℝ) ^ 4 * CE)
/-- the gradient constant of `E'` -/
noncomputable def CgE (ell : ℕ) : ℝ := 2 * GE * (8 + 6 * (ell : ℝ) ^ 4 * CE)

theorem GE_pos : 0 < GE := by unfold GE; norm_num

/-- `‖K y‖_D² ≤ 3ℓ⁴ CE ‖y‖_D²` -/
theorem Kop_D (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (y : FSp (geomOf ell k S)) : nD (Kop hell y) ≤ 3 * (ell : ℝ) ^ 4 * CE * nD y := by
  rw [Kop_eq]
  have h1 : nD ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (EflatL hell y))
      ≤ 3 * (ell : ℝ) ^ 2 * AdalyFormal.M1.wnormSq S ell k (EflatL hell y) := flat_D hell2 hS hM hR _
  have h2 := E_wnorm hell hell2 hS (by omega) hM y
  have h0 : (0 : ℝ) ≤ 3 * (ell : ℝ) ^ 2 := by positivity
  calc nD ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (EflatL hell y))
      ≤ 3 * (ell : ℝ) ^ 2 * AdalyFormal.M1.wnormSq S ell k (EflatL hell y) := h1
    _ ≤ 3 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2 * CE * nD y) := mul_le_mul_of_nonneg_left h2 h0
    _ = 3 * (ell : ℝ) ^ 4 * CE * nD y := by ring

/-- `‖2y − Ky‖_D² ≤ (8 + 6ℓ⁴CE) ‖y‖_D²` -/
theorem twoK_D (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (y : FSp (geomOf ell k S)) : nD ((2 : ℝ) • y - Kop hell y) ≤ (8 + 6 * (ell : ℝ) ^ 4 * CE) * nD y := by
  have h1 := nD_sub_le hell ((2 : ℝ) • y) (Kop hell y)
  rw [nD_smul] at h1
  have h2 := Kop_D hell hell2 hS hM hR y
  nlinarith

/-- **`‖E' y‖_w² ≤ CwE ‖y‖_D²`** -/
theorem Eright_wnorm (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (y : FSp (geomOf ell k S)) : AdalyFormal.M1.wnormSq S ell k (ErightL hell y) ≤ CwE ell * nD y := by
  rw [ErightL_apply]
  have h1 := E_wnorm hell hell2 hS (by omega) hM ((2 : ℝ) • y - Kop hell y)
  have h2 := twoK_D hell hell2 hS hM hR y
  have hc : (0 : ℝ) ≤ (ell : ℝ) ^ 2 * CE := by have := CE_pos; positivity
  unfold CwE
  calc AdalyFormal.M1.wnormSq S ell k (EflatL hell ((2 : ℝ) • y - Kop hell y))
      ≤ (ell : ℝ) ^ 2 * CE * nD ((2 : ℝ) • y - Kop hell y) := h1
    _ ≤ (ell : ℝ) ^ 2 * CE * ((8 + 6 * (ell : ℝ) ^ 4 * CE) * nD y) := mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring

/-- **`gradW (E' y) ν ≤ CgE ‖y‖_D²`** -/
theorem Eright_grad (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (y : FSp (geomOf ell k S)) (ν0 : Fin 3) : gradW (ErightL hell y) ν0 ≤ CgE ell * nD y := by
  rw [ErightL_apply]
  have h1 := E_grad hell hell2 hS ((2 : ℝ) • y - Kop hell y) ν0
  have h2 := twoK_D hell hell2 hS hM hR y
  have hc : (0 : ℝ) ≤ 2 * GE := by have := GE_pos; positivity
  unfold CgE
  calc gradW (EflatL hell ((2 : ℝ) • y - Kop hell y)) ν0 ≤ 2 * GE * nD ((2 : ℝ) • y - Kop hell y) := h1
    _ ≤ 2 * GE * ((8 + 6 * (ell : ℝ) ^ 4 * CE) * nD y) := mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring

/-- **W6 for D2: a right inverse of `Q_U` on `E₀` with weighted energy** -/
theorem bond_rightinv_strat (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (ε : ℕ → ℝ) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hsmall : 3 * (ell : ℝ) ^ 2 * delW ell k ε ^ 2 * CwE ell ≤ 1 / 4) (u : FSp (geomOf ell k S)) :
    ∃ x : ↥(bondSupp (geomOf ell k S)), (gparams ell k Lu hell S U a Lam).data.Q x = u ∧
      AdalyFormal.M1.wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ 4 * CwE ell * nD u ∧
      ∀ ν0 : Fin 3, gradW (x : BondFnL2 (scaleUp ell k Lu)) ν0 ≤ 4 * CgE ell * nD u := by
  set A : ↥(bondSupp (geomOf ell k S)) →L[ℝ] FSp (geomOf ell k S) := ((bondSectorOf (geomOf ell k S) U).Qfull).comp (iE (geomOf ell k S)) with hA
  set E2 : FSp (geomOf ell k S) →ₗ[ℝ] ↥(bondSupp (geomOf ell k S)) := LinearMap.codRestrict (bondSupp (geomOf ell k S)) (ErightL hell)
    (fun y => Eright_mem hell hS y) with hE2
  set T : FSp (geomOf ell k S) →ₗ[ℝ] FSp (geomOf ell k S) := (A : ↥(bondSupp (geomOf ell k S)) →ₗ[ℝ] FSp (geomOf ell k S)).comp E2 with hT
  have hTapp : ∀ y, T y = (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y) := fun y => rfl
  -- `T y = y − d y`, `‖d y‖_D² ≤ c ‖y‖_D²`, `c ≤ 1/4`
  set c := 3 * (ell : ℝ) ^ 2 * delW ell k ε ^ 2 * CwE ell with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ CwE ell := by unfold CwE; have := CE_pos; positivity
    positivity
  have hdrift : ∀ y, nD (y - T y) ≤ c * nD y := by
    intro y
    have hd : y - T y = (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y) - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y) := by
      rw [hTapp, Eright_rightInv hell hell2 hS hM hR y]
    rw [hd]
    have h1 := drift_D hell2 hS hM hR U ε hreg hcl hε0 hsm (ErightL hell y)
    have h1' : nD ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y) - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y))
        ≤ 3 * (ell : ℝ) ^ 2 * delW ell k ε ^ 2 * AdalyFormal.M1.wnormSq S ell k (ErightL hell y) := by
      refine le_trans (le_of_eq ?_) h1
      unfold nD
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [show ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y) - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y)) p
          = (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y) p - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y) p from rfl,
        norm_sub_rev]
    have h2 := Eright_wnorm hell hell2 hS hM hR y
    have h0 : (0 : ℝ) ≤ 3 * (ell : ℝ) ^ 2 * delW ell k ε ^ 2 := by positivity
    calc nD ((bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (ErightL hell y) - (bondSectorOf (geomOf ell k S) U).Qfull (ErightL hell y))
        ≤ 3 * (ell : ℝ) ^ 2 * delW ell k ε ^ 2 * AdalyFormal.M1.wnormSq S ell k (ErightL hell y) := h1'
      _ ≤ 3 * (ell : ℝ) ^ 2 * delW ell k ε ^ 2 * (CwE ell * nD y) := mul_le_mul_of_nonneg_left h2 h0
      _ = c * nD y := by rw [hc]; ring
  -- a priori bound: `‖y‖_D² ≤ 4 ‖T y‖_D²`
  have hapriori : ∀ y, nD y ≤ 4 * nD (T y) := by
    intro y
    have h1 := nD_add_le hell (T y) (y - T y)
    rw [add_sub_cancel] at h1
    have h2 := hdrift y
    have hy := nD_nonneg hell y
    nlinarith
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro y hy0
    have h := hapriori y
    rw [hy0] at h
    have h0 : nD (0 : FSp (geomOf ell k S)) = 0 := by unfold nD; simp
    rw [h0, mul_zero] at h
    -- nD y ≤ 0 ⇒ y = 0
    have hterm : ∀ p, wD p * ‖y p‖ ^ 2 = 0 := by
      intro p
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg (wD_pos hell p).le (sq_nonneg ‖y p‖))).mp
        (le_antisymm h (nD_nonneg hell y)) p (mem_univ p)
    refine PiLp.ext (fun p => ?_)
    have h1 := hterm p
    have hw := wD_pos hell p
    have h2 : ‖y p‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hw.ne'
      · exact h
    have : ‖y p‖ = 0 := by simpa using h2
    simpa using this
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  obtain ⟨v, hv⟩ := hTsurj u
  have hvn : nD v ≤ 4 * nD u := by have := hapriori v; rw [hv] at this; exact this
  refine ⟨E2 v, ?_, ?_, ?_⟩
  · exact hv
  · have h : AdalyFormal.M1.wnormSq S ell k ((E2 v : ↥(bondSupp (geomOf ell k S))) : BondFnL2 (scaleUp ell k Lu))
        ≤ CwE ell * nD v := Eright_wnorm hell hell2 hS hM hR v
    have hC : 0 ≤ CwE ell := by unfold CwE; have := CE_pos; positivity
    nlinarith
  · intro ν0
    have h : gradW ((E2 v : ↥(bondSupp (geomOf ell k S))) : BondFnL2 (scaleUp ell k Lu)) ν0 ≤ CgE ell * nD v :=
      Eright_grad hell hell2 hS hM hR v ν0
    have hC : 0 ≤ CgE ell := by unfold CgE; have := GE_pos; have := CE_pos; positivity
    nlinarith

end energy

end AdalyFormal.W6

#print axioms AdalyFormal.W6.gradW
#print axioms AdalyFormal.W6.norm_sq_sum_two
#print axioms AdalyFormal.W6.uprof_grad
#print axioms AdalyFormal.W6.wD
#print axioms AdalyFormal.W6.wD_pos
#print axioms AdalyFormal.W6.nD
#print axioms AdalyFormal.W6.nD_nonneg
#print axioms AdalyFormal.W6.GE
#print axioms AdalyFormal.W6.Elev_grad
#print axioms AdalyFormal.W6.Elev_diff_two
#print axioms AdalyFormal.W6.E_grad
#print axioms AdalyFormal.W6.wt_bstrat_le
#print axioms AdalyFormal.W6.E_wnorm
#print axioms AdalyFormal.W6.foot_levels_w
#print axioms AdalyFormal.W6.wD_eq
#print axioms AdalyFormal.W6.drift_D
#print axioms AdalyFormal.W6.flat_D
#print axioms AdalyFormal.W6.nD_sub_le
#print axioms AdalyFormal.W6.nD_add_le
#print axioms AdalyFormal.W6.nD_smul
#print axioms AdalyFormal.W6.CwE
#print axioms AdalyFormal.W6.CgE
#print axioms AdalyFormal.W6.GE_pos
#print axioms AdalyFormal.W6.Kop_D
#print axioms AdalyFormal.W6.twoK_D
#print axioms AdalyFormal.W6.Eright_wnorm
#print axioms AdalyFormal.W6.Eright_grad
#print axioms AdalyFormal.W6.bond_rightinv_strat
