import MI23

/-!
# MI24 -- the row drift for a GENERAL field, and the normalised block profile `φ` (M1 lane E, 2026-10-13)

* `row_drift_gen` : lane C's `row_drift` (MS6) with the block constant replaced by an arbitrary site field:
  `‖Q'_j(U) f − Q'_j(1) f‖² ≤ E² · ℓ^{−3j} Σ_x ‖f x‖²`, `E = Σ_{i<j} 6(ℓ−1)δ_i` (same tower hypothesis `hT`).
* `Sn`, `Sn_pos`; `phiB n y x = n³ T_y(x) / S_n³` (`S_n = n(n+1)(n+2)/6`) on the block, `0` off it:
  `phiB_nonneg`, `phiB_sum` (`Σ_B φ = n³`, i.e. mean one), `phiB_le` (`φ ≤ 4`).
(The step and edge bounds `phiB_step`, `phiB_out`, `phiB_in` are in MI25.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.M1Site
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.PoincareBridge (coarseLattice_fits)
open AdalyFormal.DLayer (boxF mem_boxF)

variable {L : PeriodicLatticeExtent}

/-- **row drift, general field** (copy of lane C's `row_drift` proof; only the right-hand side changes). -/
theorem row_drift_gen (G : TowerGeom L) (U : Cfg L) (ell : ℕ) (hellG : G.ell = ell) (hell : 0 < ell) (j : ℕ)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (ell ^ j)) (hdvdj : ∀ μ, ell ^ j ∣ L μ + 1)
    (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    (hT : ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (f : SiteL2 L) :
    ‖Qlev G U j y f - Qlev G (trivialU L) j y f‖ ^ 2
      ≤ (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) ^ 2 * ((1 / ((ell ^ j : ℕ) : ℝ) ^ 3) * ∑ x, ‖f x‖ ^ 2) := by
  classical
  set g : PeriodicLatticeSite L → SuTwo := WithLp.ofLp f with hg
  set Λ : Finset (PeriodicLatticeSite L) := {y} with hΛ
  have hLY : Λ ⊆ CoarseLattice L (ell ^ j) := by intro z hz; rw [Finset.mem_singleton.mp hz]; exact hy
  have hZc := chainZ_sub ell j Λ hLY
  have hchain := chainZ_step ell j Λ hLY
  have htel := NsZ_telescope_local_al ell hell (bgTower G U) δ hδ0 j (chainZ ell j Λ)
    (fun i hi ν => Dvd.dvd.trans (pow_dvd_pow ell (by omega : i ≤ j)) (hdvdj ν))
    (fun i hi => hZc i hi) (fun i hi => hchain i hi)
    (by
      intro i hi y' hy' μ
      have hy'' := hZc (i + 1) (by omega) hy'
      have hdv : ∀ ν, ell ^ (i + 1) ∣ L ν + 1 := fun ν =>
        Dvd.dvd.trans (pow_dvd_pow ell (by omega : i + 1 ≤ j)) (hdvdj ν)
      have := coarseLattice_fits hdv hy'' μ
      rwa [pow_succ] at this)
    (by
      intro i hi y' hy' z hz hzal μ hzs
      obtain ⟨y0, hy0, hsub⟩ := chainZ_block_single ell hell j Λ hLY (i + 1) (by omega) y' hy'
      rw [Finset.mem_singleton.mp hy0] at hsub
      have hz' : z ∈ blockOf y' (ell ^ (i + 1)) := by rwa [pow_succ]
      have hzs' : coarseShift z (ell ^ i) μ ∈ blockOf y' (ell ^ (i + 1)) := by rwa [pow_succ]
      exact hT i hi z (hsub hz') hzal μ (hsub hzs'))
    g j le_rfl
  rw [chainZ_top] at htel
  set E := ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun i _ => by
    have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    have := hδ0 i; positivity)
  have hbg : bgTower G (trivialU L) = fun _ => trivialU L := funext (fun i => AdalyFormal.PortSlice.bgTower_trivialU G i)
  set d := Qlev G U j y f - Qlev G (trivialU L) j y f with hd
  have hdQ : (Qcomposite (bgTower G U) ell j g - Qcomposite (fun _ => trivialU L) ell j g) y = d := by
    rw [hd, Qlev_apply, Qlev_apply, hbg, hellG]; rfl
  have hL : NsZ (ell ^ j) Λ (Qcomposite (bgTower G U) ell j g - Qcomposite (fun _ => trivialU L) ell j g) ^ 2
      = ((ell ^ j : ℕ) : ℝ) ^ 3 * ‖d‖ ^ 2 := by
    rw [NsZ_sq, hΛ, Finset.sum_singleton, hdQ]
  have hR : NsZ 1 (chainZ ell j Λ 0) g ^ 2 ≤ ∑ x, ‖f x‖ ^ 2 := by
    rw [NsZ_sq]
    have h1 : ∑ x ∈ chainZ ell j Λ 0, ‖g x‖ ^ 2 ≤ ∑ x, ‖g x‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
    simpa using h1
  have hN0 := NsZ_nonneg (ell ^ j) Λ (Qcomposite (bgTower G U) ell j g - Qcomposite (fun _ => trivialU L) ell j g)
  have hsq := pow_le_pow_left₀ hN0 htel 2
  rw [hL, mul_pow] at hsq
  have hn3 : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) ^ 3 := by have := pow_pos hell j; positivity
  have h3 : ((ell ^ j : ℕ) : ℝ) ^ 3 * ‖d‖ ^ 2 ≤ E ^ 2 * ∑ x, ‖f x‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hR (sq_nonneg E)
    linarith
  rw [div_mul_eq_mul_div, one_mul, mul_div_assoc', le_div_iff₀ hn3]
  linarith

/-! ## the normalised profile -/

/-- `S_n = n(n+1)(n+2)/6`. -/
noncomputable def Sn (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 6

theorem Sn_pos {n : ℕ} (hn : 1 ≤ n) : 0 < Sn n := by
  unfold Sn
  have : (1 : ℝ) ≤ n := (by exact_mod_cast hn)
  positivity

open Classical in
/-- the normalised tent on the block `B(y,n)`. -/
noncomputable def phiB (n : ℕ) (y x : PeriodicLatticeSite L) : ℝ :=
  if x ∈ blockOf y n then ((n : ℝ) ^ 3 / Sn n ^ 3) * ∏ μ : Fin 3, tp n ((x μ).val - (y μ).val) else 0

theorem phiB_nonneg (n : ℕ) (hn : 1 ≤ n) (y x : PeriodicLatticeSite L) : 0 ≤ phiB n y x := by
  classical
  unfold phiB
  split_ifs with hx
  · have hS := Sn_pos hn
    refine mul_nonneg (by positivity) (Finset.prod_nonneg (fun μ _ => (tp_pos ?_).le))
    rw [mem_blockOf] at hx; have := hx μ; omega
  · exact le_rfl

theorem phiB_sum (n : ℕ) (hn : 1 ≤ n) (y : PeriodicLatticeSite L) (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) :
    ∑ x ∈ blockOf y n, phiB n y x = (n : ℝ) ^ 3 := by
  classical
  have e : ∀ x ∈ blockOf y n, phiB n y x = ((n : ℝ) ^ 3 / Sn n ^ 3) * ∏ μ : Fin 3, tp n ((x μ).val - (y μ).val) := by
    intro x hx; unfold phiB; rw [if_pos hx]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, blockSum_prod y n hfit (fun _ t => tp n t)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [tp_sum n]
  have hS := Sn_pos hn
  unfold Sn at hS ⊢
  field_simp

/-- `(n+1)²/4 · n³ / S_n ≤ …`: the profile is at most `4`. -/
theorem phiB_le (n : ℕ) (hn : 1 ≤ n) (y x : PeriodicLatticeSite L) : phiB n y x ≤ 4 := by
  classical
  unfold phiB
  split_ifs with hx
  · have hS := Sn_pos hn
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hprod : ∏ μ : Fin 3, tp n ((x μ).val - (y μ).val) ≤ (((n : ℝ) + 1) ^ 2 / 4) ^ 3 := by
      rw [Fin.prod_univ_three]
      have h0 : ∀ μ : Fin 3, 0 ≤ tp n ((x μ).val - (y μ).val) := by
        intro μ; refine (tp_pos ?_).le; rw [mem_blockOf] at hx; have := hx μ; omega
      have a0 := h0 0; have a1 := h0 1; have a2 := h0 2
      have b0 : tp n ((x 0).val - (y 0).val) ≤ ((n : ℝ) + 1) ^ 2 / 4 := tp_le
      have b1 : tp n ((x 1).val - (y 1).val) ≤ ((n : ℝ) + 1) ^ 2 / 4 := tp_le
      have b2 : tp n ((x 2).val - (y 2).val) ≤ ((n : ℝ) + 1) ^ 2 / 4 := tp_le
      calc tp n ((x 0).val - (y 0).val) * tp n ((x 1).val - (y 1).val) * tp n ((x 2).val - (y 2).val)
          ≤ (((n : ℝ) + 1) ^ 2 / 4) * (((n : ℝ) + 1) ^ 2 / 4) * (((n : ℝ) + 1) ^ 2 / 4) := by
            refine mul_le_mul (mul_le_mul b0 b1 a1 (by positivity)) b2 a2 (by positivity)
        _ = (((n : ℝ) + 1) ^ 2 / 4) ^ 3 := by ring
    have hc : (0 : ℝ) ≤ (n : ℝ) ^ 3 / Sn n ^ 3 := by positivity
    refine (mul_le_mul_of_nonneg_left hprod hc).trans ?_
    have e : (n : ℝ) ^ 3 / Sn n ^ 3 * (((n : ℝ) + 1) ^ 2 / 4) ^ 3 = (27 / 8) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ 3 := by
      unfold Sn; field_simp; ring
    rw [e]
    have hq : ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hq0 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by positivity
    have h3 : (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ 3 ≤ 1 := pow_le_one₀ hq0 hq
    nlinarith
  · norm_num

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.row_drift_gen
#print axioms AdalyFormal.M1IMS.Sn_pos
#print axioms AdalyFormal.M1IMS.phiB_nonneg
#print axioms AdalyFormal.M1IMS.phiB_sum
#print axioms AdalyFormal.M1IMS.phiB_le
#print axioms AdalyFormal.M1IMS.Sn
#print axioms AdalyFormal.M1IMS.phiB
