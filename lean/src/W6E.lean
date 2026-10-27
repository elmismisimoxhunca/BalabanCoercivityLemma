import W6D
import MI32

/-!
# W6E -- row-level size and drift of the genuine `Q` on a proper tower, in the row-normalised norm (W6 lane, 2026-10-13)

`‖y‖_F² = Σ_p (ℓ^{lev p})³ ‖y_p‖²` (W6D `nF`). Under the M0-chain tower hypotheses on the blocked background of `V`
(`RegTower`, `TowerClass ε`, `ε ≥ 0`, `ρ(ε) < π/2`; BC5 `tower_FG`), with `S = Σ_{i<k} θ(ε_i)`, `r = ℓ^{-1/2}`:
* `level_drift` : `Σ_{rows of level j} ℓ^{3j} ‖(Q_V x − Q₁ x)_p‖² ≤ δ² ‖x|_{F_j}‖²`, `δ = (S/r)e^{S/r}` (`delW`), where `F_j` is the
  union of the footprints (DL28 `Foot`) of the level-`j` rows;
* `level_size` : `Σ_{rows of level j} ℓ^{3j} ‖(Q_V x)_p‖² ≤ e^{2S/r} ‖x|_{F_j}‖²`;
* `foot_levels` : a bond lies in `F_j` for at most three `j` (MI31 `row_window`, `8ℓ ≤ R`);
* **`drift_F`** : `nF (Q_V x − Q₁ x) ≤ 3 δ² ‖x‖²`;  **`flat_F`** : `nF (Q₁ x) ≤ 3 ‖x‖²` (`V = 1`, `ε = 0`).
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
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.DLayer (Foot bondRestr)
open AdalyFormal.BondComposite (tower_FG TowerClass rr thetaOf nrm nrm_sq nrm_one_suCoord nrm_nonneg suOf_sub
  thetaOf_nonneg sum_le_of_injective flatBg regTower_flat)

section drift
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- the union of the footprints of the level-`j` rows -/
def FootL (j : Fin (k + 1)) (e : Bond (scaleUp ell k Lu)) : Prop :=
  ∃ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, Foot ell (j : ℕ) r.1 e

/-- `S = Σ_{i<k} θ(ε_i)` -/
noncomputable def SS (ell k : ℕ) (ε : ℕ → ℝ) : ℝ := ∑ i ∈ range k, thetaOf ell (ε i)
/-- the drift constant `δ = (S/r) e^{S/r}` -/
noncomputable def delW (ell k : ℕ) (ε : ℕ → ℝ) : ℝ := (SS ell k ε / rr ell) * Real.exp (SS ell k ε / rr ell)
/-- the size constant `e^{S/r}` -/
noncomputable def expW (ell k : ℕ) (ε : ℕ → ℝ) : ℝ := Real.exp (SS ell k ε / rr ell)

theorem bgTower_geom_trivial :
    bgTower (geomOf ell k S) (trivialU (scaleUp ell k Lu)) = flatBg ell k Lu :=
  funext (AdalyFormal.SliceCoerc.ubarTower_trivial ell)

theorem regTower_triv (hell : 0 < ell) : RegTower ell (bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu))) k := by
  have h : bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu)) = flatBg ell k Lu :=
    funext (AdalyFormal.SliceCoerc.ubarTower_trivial ell)
  rw [h]; exact regTower_flat ell k Lu hell k

open Classical in
theorem bondRestr_norm_sq (P : Bond (scaleUp ell k Lu) → Prop) (x : BondFnL2 (scaleUp ell k Lu)) :
    ‖bondRestr P x‖ ^ 2 = ∑ e, (if P e then ‖x e‖ ^ 2 else 0) := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  show ‖(if P e then x e else 0)‖ ^ 2 = _
  split_ifs <;> simp

/-- a row of `Q_V` reads only `F_j` -/
theorem row_restrL (V : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) V) k)
    (x : BondFnL2 (scaleUp ell k Lu)) (j : Fin (k + 1))
    (r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}) :
    (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
      = (bondSectorOf (geomOf ell k S) V).Qfull (bondRestr (FootL (S := S) j) x) ⟨j, r⟩ := by
  classical
  have hb : bondRestr (Foot ell (j : ℕ) r.1) x = bondRestr (Foot ell (j : ℕ) r.1) (bondRestr (FootL (S := S) j) x) := by
    refine PiLp.ext (fun e => ?_)
    show (if Foot ell (j : ℕ) r.1 e then x e else 0)
      = (if Foot ell (j : ℕ) r.1 e then (if FootL (S := S) j e then x e else 0) else 0)
    by_cases he : Foot ell (j : ℕ) r.1 e
    · rw [if_pos he, if_pos he, if_pos ⟨r, he⟩]
    · rw [if_neg he, if_neg he]
  have h1 := AdalyFormal.M1IMS.Qrow_restr V hreg x ⟨j, r⟩
  have h2 := AdalyFormal.M1IMS.Qrow_restr V hreg (bondRestr (FootL (S := S) j) x) ⟨j, r⟩
  rw [h1, h2]
  exact congrArg (fun z => (bondSectorOf (geomOf ell k S) V).Qfull z ⟨j, r⟩) hb

/-- rows of one level against the whole level-`j` coarse sum -/
theorem rows_le_nrm (hell : 0 < ell) (j : Fin (k + 1)) (Z : XS (scaleUp ell k Lu)) :
    ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ‖suOf (Z r.1)‖ ^ 2
      ≤ nrm (ell ^ (j : ℕ)) Z ^ 2 := by
  classical
  rw [nrm_sq]
  have h := sum_le_of_injective (rowCBj (S := S) hell j) (rowCBj_inj hell j)
    (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ)) => ‖suOf (Z (c.1.1, c.2))‖ ^ 2) (fun _ => sq_nonneg _)
  exact h

theorem SS_mono (hell : 0 < ell) (ε : ℕ → ℝ) (hε0 : ∀ j, j < k → 0 ≤ ε j) {j : ℕ} (hj : j ≤ k) :
    ∑ i ∈ range j, thetaOf ell (ε i) ≤ SS ell k ε :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
    (fun i hi _ => thetaOf_nonneg ell (ε i) (hε0 i (Finset.mem_range.mp hi)))

theorem SS_nonneg (ε : ℕ → ℝ) (hε0 : ∀ j, j < k → 0 ≤ ε j) : 0 ≤ SS ell k ε :=
  Finset.sum_nonneg (fun i hi => thetaOf_nonneg ell (ε i) (hε0 i (Finset.mem_range.mp hi)))

theorem rr_pos (hell : 0 < ell) : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)

/-- `(r^j)² · ℓ^{3j} · (ℓ^j)^{-2} = 1` -/
theorem scale_one (hell : 0 < ell) (j : ℕ) :
    ((ell : ℝ) ^ j) ^ 3 * (((ell : ℝ) ^ j)⁻¹) ^ 2 * ((rr ell) ^ j) ^ 2 = 1 := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hr2 : (rr ell) ^ 2 = (ell : ℝ)⁻¹ := by
    rw [AdalyFormal.BondComposite.rr_sq ell hell, one_div]
  have h1 : ((rr ell) ^ j) ^ 2 = ((ell : ℝ) ^ j)⁻¹ := by
    rw [← pow_mul, mul_comm, pow_mul, hr2, inv_pow]
  rw [h1]
  field_simp

/-- **level-`j` drift** -/
theorem level_drift (hell : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) V) k) (hcl : TowerClass ell k Lu V ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (j : Fin (k + 1)) (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ delW ell k ε ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set xr := bondRestr (FootL (S := S) j) x with hxr
  set Z : XS (scaleUp ell k Lu) := QlinCompX ell (bgTower (GF ell k Lu) V) (j : ℕ) (suCoord xr)
      - QlinCompX ell (flatBg ell k Lu) (j : ℕ) (suCoord xr) with hZ
  have hrow : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩ - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩
        = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (Z r.1) := by
    intro r
    rw [row_restrL V hreg x j r, row_restrL (trivialU _) (regTower_triv hell) x j r]
    have hregV : RegTower (geomOf ell k S).ell (bgTower (geomOf ell k S) V) (geomOf ell k S).k := hreg
    have hreg1 : RegTower (geomOf ell k S).ell (bgTower (geomOf ell k S) (trivialU _)) (geomOf ell k S).k :=
      regTower_triv hell
    rw [AdalyFormal.BondComposite.Qfull_apply_level ell k Lu (geomOf ell k S) V hregV xr ⟨j, r⟩,
      AdalyFormal.BondComposite.Qfull_apply_level ell k Lu (geomOf ell k S) (trivialU _) hreg1 xr ⟨j, r⟩]
    show ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompX ell (bgTower (GF ell k Lu) V) (j : ℕ) (suCoord xr) r.1)
        - ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (QlinCompX ell (bgTower (geomOf ell k S) (trivialU _)) (j : ℕ) (suCoord xr) r.1)
        = _
    rw [bgTower_geom_trivial, ← smul_sub, ← suOf_sub, hZ]
    rfl
  have hFG := (tower_FG ell k Lu hell V ε hreg hcl hε0 hsm (suCoord xr) (j : ℕ) hjk).2
  rw [nrm_one_suCoord] at hFG
  set Sj := ∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i) with hSj
  have hr := rr_pos hell
  have hSjle := SS_mono hell ε hε0 hjk
  have hSj0 : 0 ≤ Sj := Finset.sum_nonneg (fun i hi => thetaOf_nonneg ell (ε i)
    (hε0 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hjk)))
  have hδ : (Sj / rr ell) * Real.exp (Sj / rr ell) ≤ delW ell k ε := by
    unfold delW
    have h1 : Sj / rr ell ≤ SS ell k ε / rr ell := div_le_div_of_nonneg_right hSjle hr.le
    have h0 : 0 ≤ Sj / rr ell := div_nonneg hSj0 hr.le
    exact mul_le_mul h1 (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (le_trans h0 h1)
  have hδ0 : 0 ≤ (Sj / rr ell) * Real.exp (Sj / rr ell) := mul_nonneg (div_nonneg hSj0 hr.le) (Real.exp_pos _).le
  have hnZ : nrm (ell ^ (j : ℕ)) Z ≤ (rr ell) ^ (j : ℕ) * delW ell k ε * ‖xr‖ := by
    have hrj : 0 ≤ (rr ell) ^ (j : ℕ) := pow_nonneg hr.le _
    calc nrm (ell ^ (j : ℕ)) Z ≤ (rr ell) ^ (j : ℕ) * (Sj / rr ell) * Real.exp (Sj / rr ell) * ‖xr‖ := hFG
      _ = (rr ell) ^ (j : ℕ) * ((Sj / rr ell) * Real.exp (Sj / rr ell)) * ‖xr‖ := by ring
      _ ≤ (rr ell) ^ (j : ℕ) * delW ell k ε * ‖xr‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ hrj) (norm_nonneg _)
  have hnZ2 : nrm (ell ^ (j : ℕ)) Z ^ 2 ≤ ((rr ell) ^ (j : ℕ) * delW ell k ε * ‖xr‖) ^ 2 :=
    pow_le_pow_left₀ (nrm_nonneg _ _) hnZ 2
  have hsum := rows_le_nrm (S := S) hell j Z
  calc ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
          - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      = ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ‖suOf (Z r.1)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [hrow r, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
        ring
    _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * nrm (ell ^ (j : ℕ)) Z ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ) * delW ell k ε * ‖xr‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hnZ2 (by positivity)
    _ = (((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ)) ^ 2)
          * (delW ell k ε ^ 2 * ‖xr‖ ^ 2) := by ring
    _ = delW ell k ε ^ 2 * ‖xr‖ ^ 2 := by rw [scale_one hell, one_mul]

/-- **level-`j` size** -/
theorem level_size (hell : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) V) k) (hcl : TowerClass ell k Lu V ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (j : Fin (k + 1)) (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ expW ell k ε ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set xr := bondRestr (FootL (S := S) j) x with hxr
  set Z : XS (scaleUp ell k Lu) := QlinCompX ell (bgTower (GF ell k Lu) V) (j : ℕ) (suCoord xr) with hZ
  have hrow : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      (bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩ = ((ell : ℝ) ^ (j : ℕ))⁻¹ • suOf (Z r.1) := by
    intro r
    rw [row_restrL V hreg x j r]
    have hregV : RegTower (geomOf ell k S).ell (bgTower (geomOf ell k S) V) (geomOf ell k S).k := hreg
    rw [AdalyFormal.BondComposite.Qfull_apply_level ell k Lu (geomOf ell k S) V hregV xr ⟨j, r⟩]
    rfl
  have hFG := (tower_FG ell k Lu hell V ε hreg hcl hε0 hsm (suCoord xr) (j : ℕ) hjk).1
  rw [nrm_one_suCoord] at hFG
  set Sj := ∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε i) with hSj
  have hr := rr_pos hell
  have hSjle := SS_mono hell ε hε0 hjk
  have hE : Real.exp (Sj / rr ell) ≤ expW ell k ε := by
    unfold expW
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hSjle hr.le)
  have hnZ : nrm (ell ^ (j : ℕ)) Z ≤ (rr ell) ^ (j : ℕ) * expW ell k ε * ‖xr‖ := by
    have hrj : 0 ≤ (rr ell) ^ (j : ℕ) := pow_nonneg hr.le _
    calc nrm (ell ^ (j : ℕ)) Z ≤ (rr ell) ^ (j : ℕ) * Real.exp (Sj / rr ell) * ‖xr‖ := hFG
      _ ≤ (rr ell) ^ (j : ℕ) * expW ell k ε * ‖xr‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hrj) (norm_nonneg _)
  have hnZ2 : nrm (ell ^ (j : ℕ)) Z ^ 2 ≤ ((rr ell) ^ (j : ℕ) * expW ell k ε * ‖xr‖) ^ 2 :=
    pow_le_pow_left₀ (nrm_nonneg _ _) hnZ 2
  have hsum := rows_le_nrm (S := S) hell j Z
  calc ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        ((ell : ℝ) ^ (j : ℕ)) ^ 3 * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩‖ ^ 2
      = ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2
          * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ‖suOf (Z r.1)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [hrow r, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (pow_pos hellR _)]
        ring
    _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * nrm (ell ^ (j : ℕ)) Z ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ) * expW ell k ε * ‖xr‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hnZ2 (by positivity)
    _ = (((ell : ℝ) ^ (j : ℕ)) ^ 3 * (((ell : ℝ) ^ (j : ℕ))⁻¹) ^ 2 * ((rr ell) ^ (j : ℕ)) ^ 2)
          * (expW ell k ε ^ 2 * ‖xr‖ ^ 2) := by ring
    _ = expW ell k ε ^ 2 * ‖xr‖ ^ 2 := by rw [scale_one hell, one_mul]

open Classical in
/-- **a bond lies in at most three level footprints** -/
theorem foot_levels (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ j : Fin (k + 1), ‖bondRestr (FootL (S := S) j) x‖ ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
  simp only [bondRestr_norm_sq]
  rw [Finset.sum_comm, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  set s := AdalyFormal.M1.strat S k e.1
  have hle : ∀ j : Fin (k + 1), (if FootL (S := S) j e then ‖x e‖ ^ 2 else 0)
      ≤ (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0) * ‖x e‖ ^ 2 := by
    intro j
    by_cases hF : FootL (S := S) j e
    · obtain ⟨r, hr⟩ := hF
      have hw := AdalyFormal.M1IMS.row_window (κ := 1) (c := 5) hS Nat.one_pos hM hell2 (by omega) (by omega)
        le_rfl (⟨j, r⟩ : BIdx (geomOf ell k S)) e hr
      rw [if_pos ⟨r, hr⟩, if_pos hw, one_mul]
    · rw [if_neg hF]; split_ifs <;> simp
  refine (Finset.sum_le_sum (fun j _ => hle j)).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (AdalyFormal.M1IMS.levels_le_three k s) (sq_nonneg _)

/-- **drift in the row-normalised norm** -/
theorem drift_F (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (V : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) V) k) (hcl : TowerClass ell k Lu V ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wF p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
      ≤ 3 * delW ell k ε ^ 2 * ‖x‖ ^ 2 := by
  have hell : 0 < ell := by omega
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wF p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p
      - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2)]
  calc ∑ j : Fin (k + 1), ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        wF (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
          - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ ∑ j : Fin (k + 1), delW ell k ε ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => level_drift hell V ε hreg hcl hε0 hsm j x)
    _ = delW ell k ε ^ 2 * ∑ j : Fin (k + 1), ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ delW ell k ε ^ 2 * (3 * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (foot_levels hell2 hS hM hR x) (sq_nonneg _)
    _ = 3 * delW ell k ε ^ 2 * ‖x‖ ^ 2 := by ring

/-- the flat background is in the tower class with `ε = 0` -/
theorem towerClass_triv (hell : 0 < ell) : TowerClass ell k Lu (trivialU (scaleUp ell k Lu)) (fun _ => 0) := by
  intro j _ y _ μ
  have h : bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu)) j = trivialU (scaleUp ell k Lu) :=
    AdalyFormal.SliceCoerc.ubarTower_trivial ell j
  rw [h, AdalyFormal.BondComposite.frob_trivial_sub_one]

theorem rhoOf_zero_lt (ell : ℕ) : rhoOf ell 0 < Real.pi / 2 := by
  have : rhoOf ell 0 = 0 := by unfold rhoOf; simp
  rw [this]; positivity

theorem expW_zero (hell : 0 < ell) : expW ell k (fun _ => 0) = 1 := by
  unfold expW SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]

/-- **the flat `Q` in the row-normalised norm: `nF(Q₁ x) ≤ 3 ‖x‖²`** -/
theorem flat_F (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wF p * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
  have hell : 0 < ell := by omega
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wF p * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2)]
  calc ∑ j : Fin (k + 1), ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        wF (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ ∑ j : Fin (k + 1), expW ell k (fun _ => 0) ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => level_size hell (trivialU _) (fun _ => 0) (regTower_triv hell)
          (towerClass_triv hell) (fun _ _ => le_rfl) (fun _ _ => rhoOf_zero_lt ell) j x)
    _ = ∑ j : Fin (k + 1), ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by
        rw [expW_zero hell]; simp
    _ ≤ 3 * ‖x‖ ^ 2 := foot_levels hell2 hS hM hR x

end drift

end AdalyFormal.W6

#print axioms AdalyFormal.W6.FootL
#print axioms AdalyFormal.W6.SS
#print axioms AdalyFormal.W6.delW
#print axioms AdalyFormal.W6.expW
#print axioms AdalyFormal.W6.bgTower_geom_trivial
#print axioms AdalyFormal.W6.regTower_triv
#print axioms AdalyFormal.W6.bondRestr_norm_sq
#print axioms AdalyFormal.W6.row_restrL
#print axioms AdalyFormal.W6.rows_le_nrm
#print axioms AdalyFormal.W6.SS_mono
#print axioms AdalyFormal.W6.SS_nonneg
#print axioms AdalyFormal.W6.rr_pos
#print axioms AdalyFormal.W6.scale_one
#print axioms AdalyFormal.W6.level_drift
#print axioms AdalyFormal.W6.level_size
#print axioms AdalyFormal.W6.foot_levels
#print axioms AdalyFormal.W6.drift_F
#print axioms AdalyFormal.W6.towerClass_triv
#print axioms AdalyFormal.W6.rhoOf_zero_lt
#print axioms AdalyFormal.W6.expW_zero
#print axioms AdalyFormal.W6.flat_F
