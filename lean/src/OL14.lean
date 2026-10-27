import OL13

/-!
# OL14 -- the energy right inverse from a COVARIANTLY smooth right inverse (no link smallness) (lane m2_oplayer_20261015)

DU1's `curl_upper` / `div_upper` bound the covariant curl / divergence by PLAIN gradients plus a link term `ρL`
(`|V_b − 1| ≤ ρL ℓ^{-bstrat b}` on EVERY bond: a global gauge).  With the COVARIANT gradient
`gradWU V B μ = Σ_b ‖R(V(b₋,μ)) B(b₋+μ, b.dir) − B b‖²` no link term appears at all:
* `curl_upper_cov` : `‖χ C_V B‖² ≤ 12 Σ_ν gradWU V B ν`;  `div_upper_cov` : `‖D_V* B‖² ≤ 3 Σ_ν gradWU V B ν`;
* `ginv_upper_cov` : DU1 `ginv_upper` with `15 Σ gradWU` in place of `30 Σ gradW + (96ℓ²+24)ρL² wnormSq`;
* **`hext_of_rightinv_cov`** : DU1 `hext_of_rightinv` for a right inverse with `wnormSq x ≤ cW nD u`,
  `gradWU V x ν ≤ cG nD u` — the energy constant is `(1+η)·45 cG/a + ν cW/a + (1+η)`.
No gauge, no chart: valid at every configuration with `HatPack` and the holonomy regime.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2 periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift gradCovariantAdjointValue)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.M1 (strat bstrat wnormSq strat_adj)
open AdalyFormal.W6 (gradW nD wD)

section upcov
variable {Lf : PeriodicLatticeExtent}

/-- the covariant shift-gradient energy in direction `μ` -/
noncomputable def gradWU (V : Cfg Lf) (B : BondFnL2 Lf) (μ : Fin 3) : ℝ :=
  ∑ b : Bond Lf, ‖RMap (V (b.1, μ)) (B (periodicLatticeShift b.1 μ, b.2)) - B b‖ ^ 2

theorem gradWU_nonneg (V : Cfg Lf) (B : BondFnL2 Lf) (μ : Fin 3) : 0 ≤ gradWU V B μ := by
  unfold gradWU; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- covariant gradient sub-sum -/
theorem gradWU_sub (V : Cfg Lf) (B : BondFnL2 Lf) (μ ν : Fin 3) :
    ∑ x : PeriodicLatticeSite Lf, ‖RMap (V (x, μ)) (B (periodicLatticeShift x μ, ν)) - B (x, ν)‖ ^ 2 ≤ gradWU V B μ := by
  unfold gradWU
  rw [show (Finset.univ : Finset (Bond Lf)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product_right]
  exact Finset.single_le_sum (f := fun ν' => ∑ x : PeriodicLatticeSite Lf,
    ‖RMap (V (x, μ)) (B (periodicLatticeShift x μ, ν')) - B (x, ν')‖ ^ 2) (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.mem_univ ν)

theorem gradWU_le_sum (V : Cfg Lf) (B : BondFnL2 Lf) (μ : Fin 3) : gradWU V B μ ≤ ∑ ν : Fin 3, gradWU V B ν :=
  Finset.single_le_sum (f := fun ν => gradWU V B ν) (fun ν _ => gradWU_nonneg V B ν) (Finset.mem_univ μ)

/-- `‖R(g)⁻¹ a − b‖ = ‖a − R(g) b‖` -/
theorem RMap_inv_sub_eq (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (a b : SuTwo) :
    ‖RMap g⁻¹ a - b‖ = ‖a - RMap g b‖ := by
  have e1 : RMap g (RMap g⁻¹ a) = a := by
    have h := LinearMap.congr_fun (AdalyFormal.Balaban.CovariantOperators.RMap_mul g g⁻¹) a
    rw [mul_inv_cancel, AdalyFormal.Balaban.CovariantOperators.RMap_one] at h
    simpa using h.symm
  have e : RMap g (RMap g⁻¹ a - b) = a - RMap g b := by rw [map_sub, e1]
  rw [← AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap g (RMap g⁻¹ a - b), e]

/-- **the covariant curl by covariant gradients** (no link term) -/
theorem curl_upper_cov (V : Cfg Lf) (S : Tower Lf) (B : BondFnL2 Lf) :
    ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 V B)‖ ^ 2 ≤ 12 * ∑ ν : Fin 3, gradWU V B ν := by
  classical
  have hmask : ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 V B)‖ ^ 2 ≤ ‖curlCovariantLM_L2 V B‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [plaqMask_apply]; split_ifs
    · exact le_rfl
    · rw [norm_zero, zero_pow two_ne_zero]; exact sq_nonneg _
  refine hmask.trans ?_
  set Gs := ∑ ν : Fin 3, gradWU V B ν
  have hpt : ∀ p : PeriodicLatticePlaquette Lf, ‖(curlCovariantLM_L2 V B) p‖ ^ 2
      ≤ 2 * (‖RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) - B (p.1, p.2.1.2)‖ ^ 2
        + ‖RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (p.1, p.2.1.1)‖ ^ 2) := by
    intro p
    rw [curlLM_apply]
    unfold curlValueCovariant
    have e : (WithLp.ofLp B) (p.1, p.2.1.1) + RMap (V (p.1, p.2.1.1)) ((WithLp.ofLp B) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - RMap (V (p.1, p.2.1.2)) ((WithLp.ofLp B) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - (WithLp.ofLp B) (p.1, p.2.1.2)
        = (RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) - B (p.1, p.2.1.2))
          - (RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (p.1, p.2.1.1)) := by
      show B (p.1, p.2.1.1) + RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (p.1, p.2.1.2) = _
      abel
    rw [e]
    set u1 := RMap (V (p.1, p.2.1.1)) (B (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) - B (p.1, p.2.1.2)
    set u2 := RMap (V (p.1, p.2.1.2)) (B (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - B (p.1, p.2.1.1)
    have t : ‖u1 - u2‖ ≤ ‖u1‖ + ‖u2‖ := norm_sub_le u1 u2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) t 2
    nlinarith [sq_nonneg (‖u1‖ - ‖u2‖)]
  rw [PiLp.norm_sq_eq_of_L2]
  refine (Finset.sum_le_sum (fun p _ => hpt p)).trans ?_
  rw [Fintype.sum_prod_type_right]
  have hd : ∀ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite Lf,
      2 * (‖RMap (V (x, d.1.1)) (B (periodicLatticeShift x d.1.1, d.1.2)) - B (x, d.1.2)‖ ^ 2
        + ‖RMap (V (x, d.1.2)) (B (periodicLatticeShift x d.1.2, d.1.1)) - B (x, d.1.1)‖ ^ 2)
      ≤ 4 * Gs := by
    intro d
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have a1 := (gradWU_sub V B d.1.1 d.1.2).trans (gradWU_le_sum V B d.1.1)
    have a2 := (gradWU_sub V B d.1.2 d.1.1).trans (gradWU_le_sum V B d.1.2)
    linarith
  calc ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite Lf, _ ≤
        ∑ _d : PeriodicPlaquetteDirections, 4 * Gs := Finset.sum_le_sum (fun d _ => hd d)
    _ = 12 * Gs := by
        rw [Finset.sum_const, Finset.card_univ, card_dirs]; simp; ring

/-- **the covariant divergence by covariant gradients** (no link term) -/
theorem div_upper_cov (V : Cfg Lf) (B : BondFnL2 Lf) :
    ‖gradAdj V B‖ ^ 2 ≤ 3 * ∑ ν : Fin 3, gradWU V B ν := by
  classical
  set s : Fin 3 → PeriodicLatticeSite Lf → ℝ := fun μ y =>
    ‖B (periodicLatticeShiftBack y μ, μ) - RMap (V (periodicLatticeShiftBack y μ, μ)) (B (y, μ))‖
  have hpt : ∀ y, ‖(gradAdj V B) y‖ ^ 2 ≤ 3 * ∑ μ : Fin 3, s μ y ^ 2 := by
    intro y
    show ‖(WithLp.ofLp (gradAdj V B)) y‖ ^ 2 ≤ _
    rw [gradAdj_apply]
    unfold gradCovariantAdjointValue
    have t : ‖∑ μ : Fin 3, (RMap (V (periodicLatticeShiftBack y μ, μ))⁻¹ ((WithLp.ofLp B) (periodicLatticeShiftBack y μ, μ))
          - (WithLp.ofLp B) (y, μ))‖ ≤ ∑ μ : Fin 3, s μ y := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun μ _ => le_of_eq ?_))
      exact RMap_inv_sub_eq _ _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) t 2
    refine h2.trans ?_
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (s 0 y - s 1 y), sq_nonneg (s 0 y - s 2 y), sq_nonneg (s 1 y - s 2 y)]
  have hre : ∀ (μ : Fin 3) (g : Bond Lf → PeriodicLatticeSite Lf → ℝ),
      ∑ y : PeriodicLatticeSite Lf, g (periodicLatticeShiftBack y μ, μ) y
        = ∑ x : PeriodicLatticeSite Lf, g (x, μ) (periodicLatticeShift x μ) := by
    intro μ g
    rw [← sum_shift_site μ (fun y => g (periodicLatticeShiftBack y μ, μ) y)]
    simp only [periodicLatticeShiftBack_shift]
  have hs : ∀ μ, ∑ y, s μ y ^ 2 ≤ gradWU V B μ := by
    intro μ
    have := hre μ (fun b y => ‖B b - RMap (V b) (B (y, b.2))‖ ^ 2)
    simp only at this
    show ∑ y, ‖B (periodicLatticeShiftBack y μ, μ) - RMap (V (periodicLatticeShiftBack y μ, μ)) (B (y, μ))‖ ^ 2 ≤ _
    rw [this]
    refine le_trans (le_of_eq ?_) (gradWU_sub V B μ μ)
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [norm_sub_rev]
  rw [PiLp.norm_sq_eq_of_L2]
  refine (Finset.sum_le_sum (fun y _ => hpt y)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs' := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => hs μ)
  linarith

end upcov

section ginvupcov
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {W : ℕ}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M) (hW : 1 ≤ W)
  (hWR : W ≤ R * M * ell)
include hS hell hR1 hM1 hW hWR

theorem ginv_upper_cov (hell0 : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (a cs : ℝ)
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) V a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k V ρ) (ε1 : ℝ) (hε1 : 0 < ε1)
    (Lam : Set (PeriodicLatticeSite Lu)) (A : ↥(bondSupp (geomOf ell k S))) :
    ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Ginv A⟫
      ≤ (1 + etaS ell W cs ρ ε1) * (15 * ∑ ν : Fin 3, gradWU V (A : BondFnL2 (scaleUp ell k Lu)) ν
          + ‖Ymass (geomOf ell k S) V a (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) := by
  have hF := ginv_form hell0 S V a Lam hp.ha.le hp.hu A
  have hsw := (sandwich hS hell hR1 hM1 hW hWR V a cs hp ρ hρ hreg ε1 hε1 (A : BondFnL2 (scaleUp ell k Lu))).2
  have e : ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Ginv A⟫ = Fform S ell k V a (A : BondFnL2 (scaleUp ell k Lu)) := by
    rw [hF]; rfl
  rw [e]
  refine hsw.trans ?_
  have hc := curl_upper_cov V S (A : BondFnL2 (scaleUp ell k Lu))
  have hd := div_upper_cov V (A : BondFnL2 (scaleUp ell k Lu))
  have hT : ‖Tfull (geomOf ell k S) V (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2
      ≤ ‖gradAdj V (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (Rproj_norm_le (geomOf ell k S) V _) 2
  have hN := N_le_wnorm hS hell0 (A : BondFnL2 (scaleUp ell k Lu))
  have hη : 0 ≤ 1 + (ε1 + (1 + 1 / ε1) * (12 * ρ ^ 2 * (ell : ℝ) ^ 8 * (4 * ell / cs) ^ 2)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) *
          ((ell : ℝ) * (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))) ^ 2) := by
    have hlg : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega))
    have hq : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := by positivity
    have h := etaS_nonneg ell W cs ρ ε1 hp.hcs hρ hε1 (by linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)])
    unfold etaS at h; linarith
  have hν : 0 ≤ 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) := by positivity
  unfold G0form etaS
  have hG : ‖plaqMask (plaqIn (S.Om 0)) (curlCovariantLM_L2 V (A : BondFnL2 (scaleUp ell k Lu)))‖ ^ 2
        + ‖Tfull (geomOf ell k S) V (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2
        + ‖Ymass (geomOf ell k S) V a (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2
      ≤ 15 * ∑ ν : Fin 3, gradWU V (A : BondFnL2 (scaleUp ell k Lu)) ν
          + ‖Ymass (geomOf ell k S) V a (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hG hη
  have := mul_le_mul_of_nonneg_left hN hν
  linarith

/-- **the energy right inverse from a COVARIANTLY smooth right inverse** -/
theorem hext_of_rightinv_cov (hell0 : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (a cs : ℝ)
    (hp : HatPack (ell := ell) (k := k) (S := S) (W := W) V a cs)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k V ρ) (ε1 : ℝ) (hε1 : 0 < ε1)
    (Lam : Set (PeriodicLatticeSite Lu)) (cW cG : ℝ) (hcW : 0 ≤ cW) (hcG : 0 ≤ cG)
    (hR : ∀ u : FSp (geomOf ell k S), ∃ x : ↥(bondSupp (geomOf ell k S)),
      (gparams ell k Lu hell0 S V a Lam).data.Q x = u ∧
      wnormSq S ell k (x : BondFnL2 (scaleUp ell k Lu)) ≤ cW * nD u ∧
      ∀ ν0 : Fin 3, gradWU V (x : BondFnL2 (scaleUp ell k Lu)) ν0 ≤ cG * nD u)
    (v : FSp (geomOf ell k S)) :
    ∃ g : ↥(bondSupp (geomOf ell k S)), (gparams ell k Lu hell0 S V a Lam).data.Q g = v ∧
      ⟪g, (gparams ell k Lu hell0 S V a Lam).data.Ginv g⟫
        ≤ ((1 + etaS ell W cs ρ ε1) * (45 * cG) / a
            + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * cW / a + (1 + etaS ell W cs ρ ε1))
          * ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 := by
  obtain ⟨x, hx, hw, hg⟩ := hR v
  refine ⟨x, hx, ?_⟩
  have ha := hp.ha
  have hup := ginv_upper_cov hS hell hR1 hM1 hW hWR hell0 V a cs hp ρ hρ hreg ε1 hε1 Lam x
  -- the mass term is `‖√w v‖²`
  have hY : Ymass (geomOf ell k S) V a (x : BondFnL2 (scaleUp ell k Lu))
      = diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v := by
    rw [← hx]; rfl
  rw [hY] at hup
  -- `nD v = ‖√w v‖² / a`
  have hnD : nD v * a = ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    unfold nD
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [diagW_apply', norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by unfold massW; positivity)]
    unfold wD massW; rw [show (((geomOf ell k S).ell : ℕ) : ℝ) = (ell : ℝ) from rfl]; ring
  set Nv := ‖diagW (geomOf ell k S) (fun p => Real.sqrt (massW (geomOf ell k S) a p)) v‖ ^ 2 with hNv
  have hnD' : nD v = Nv / a := by rw [eq_div_iff ha.ne']; exact hnD
  have hgs : ∑ ν : Fin 3, gradWU V (x : BondFnL2 (scaleUp ell k Lu)) ν ≤ 3 * (cG * nD v) := by
    rw [Fin.sum_univ_three]; have := hg 0; have := hg 1; have := hg 2; linarith
  rw [hnD'] at hgs hw
  have hη := etaS_nonneg ell W cs ρ ε1 hp.hcs hρ hε1 (by
    have : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := by
      have : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega)); positivity
    linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)])
  have hν : 0 ≤ 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) := by positivity
  have hNv0 : 0 ≤ Nv := sq_nonneg _
  have h1 : 15 * ∑ ν : Fin 3, gradWU V (x : BondFnL2 (scaleUp ell k Lu)) ν + Nv
      ≤ (45 * cG) / a * Nv + Nv := by
    have e : (45 * cG) / a * Nv = 15 * (3 * (cG * (Nv / a))) := by
      field_simp; ring
    rw [e]; linarith
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 + etaS ell W cs ρ ε1 by linarith)
  have h4 := mul_le_mul_of_nonneg_left hw hν
  have e2 : ((1 + etaS ell W cs ρ ε1) * (45 * cG) / a
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * cW / a + (1 + etaS ell W cs ρ ε1)) * Nv
      = (1 + etaS ell W cs ρ ε1) * ((45 * cG) / a * Nv + Nv)
        + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * (cW * (Nv / a)) := by
    field_simp; ring
  rw [e2]
  unfold etaS at hup h3 ⊢
  linarith

end ginvupcov

end AdalyFormal.M1DStrat

#print axioms AdalyFormal.M1DStrat.gradWU
#print axioms AdalyFormal.M1DStrat.gradWU_nonneg
#print axioms AdalyFormal.M1DStrat.gradWU_sub
#print axioms AdalyFormal.M1DStrat.gradWU_le_sum
#print axioms AdalyFormal.M1DStrat.RMap_inv_sub_eq
#print axioms AdalyFormal.M1DStrat.curl_upper_cov
#print axioms AdalyFormal.M1DStrat.div_upper_cov
#print axioms AdalyFormal.M1DStrat.ginv_upper_cov
#print axioms AdalyFormal.M1DStrat.hext_of_rightinv_cov
