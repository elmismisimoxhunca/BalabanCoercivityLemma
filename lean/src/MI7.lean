import MI5
import MI6

/-!
# MI7 -- the stratified log-weight `ψ` satisfies the hatted-chain commutator hypotheses (M1 lane E)

On `G = geomOf ell k S` (admissible, `1 ≤ W ≤ R M ℓ`, `R, M ≥ 1`, `ℓ ≥ 2`), with `θ = 2ℓ² ln ℓ / W`, `δ₀ = 3 ℓ ln ℓ / W`:
* `cjm_site_bond`, `cjm_site_yp` : `cjm` at `φ` is `cjp` at `−φ`;  `pdist_block_le` : `pdist ≤ 3(n − 1)` in a block;
* `psi_bond` (`psi_bond_neg`) : `|ψ(b₋) − ψ(b₊)| ≤ θ / ℓ^{stratG b₊}` for every bond (MI5 `psiW_lip` + MI6 `strat_eq_stratG`);
* `psi_block` (`psi_block_neg`) : `|ψ(y) − ψ(x)| ≤ δ₀` on every constraint block (MI5 `psiW_osc`);
* `theta_nonneg`, `delta0_nonneg`;
* `psi_hD`, `psi_hQ` : the four commutator bounds of the hatted `D̂, Q̂` at the weights `e^{±ψ}`
  (the `SiteHyp` instances `psiHypP`, `psiHypN` are built in MI8).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist pcd)
open AdalyFormal.StatementLaneR8 (pdist_comm pcd_le_diff)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)

variable {L : PeriodicLatticeExtent}

/-! ## 1. `cjm` at `φ` is `cjp` at `−φ` -/

theorem cjm_site_bond (φ : PeriodicLatticeSite L → ℝ) (T : SiteL2 L →L[ℝ] BondFnL2 L) :
    cjm (siteWP φ) (bondWP φ) T = cjp (siteWP (-φ)) (bondWP (-φ)) T := by
  ext1 f
  simp only [cjm, cjp, ContinuousLinearMap.comp_apply]
  show bondWt (-φ) (T (siteWt φ f)) = bondWt (-φ) (T (siteWt (-(-φ)) f))
  rw [neg_neg]

theorem cjm_site_yp (G : TowerGeom L) (φ : PeriodicLatticeSite L → ℝ) (T : SiteL2 L →L[ℝ] YP G) :
    cjm (siteWP φ) (ypWP G φ) T = cjp (siteWP (-φ)) (ypWP G (-φ)) T := by
  ext1 f
  simp only [cjm, cjp, ContinuousLinearMap.comp_apply]
  show ypWt G (-φ) (T (siteWt φ f)) = ypWt G (-φ) (T (siteWt (-(-φ)) f))
  rw [neg_neg]

/-- ℓ¹ diameter of a block. -/
theorem pdist_block_le {Lf : PeriodicLatticeExtent} {y x : PeriodicLatticeSite Lf} {n : ℕ} (hx : x ∈ blockOf y n) : pdist y x ≤ 3 * (n - 1) := by
  rw [mem_blockOf] at hx
  unfold pdist
  have h : ∀ μ : Fin 3, pcd (Lf μ + 1) (y μ).val (x μ).val ≤ n - 1 := by
    intro μ
    refine (pcd_le_diff _ _ _ (hx μ).1).trans ?_
    have := (hx μ).2; omega
  rw [Fin.sum_univ_three]
  have := h 0; have := h 1; have := h 2
  omega

/-! ## 2. `ψ` on the geometry of an admissible tower -/

section psi
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} (hS : Admissible ell M R k S)
  {W : ℕ} (hW : 1 ≤ W) (hell : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (hWR : W ≤ R * M * ell)
include hS hW hell hR hM hWR

/-- the bond condition of `hatD_comm` for `ψ`. -/
theorem psi_bond (b : Bond Lf) :
    |psiW S W ell k b.1 - psiW S W ell k (periodicLatticeShift b.1 b.2)|
      ≤ (2 * (ell : ℝ) ^ 2 * Real.log ell / W) / (ell : ℝ) ^ stratG (geomOf ell k S) (periodicLatticeShift b.1 b.2) := by
  have h := (psiW_lip hS hW (by omega) hR hM hWR b.1 b.2).1
  rwa [strat_eq_stratG (by omega) hS] at h

theorem psi_bond_neg (b : Bond Lf) :
    |(-psiW S W ell k) b.1 - (-psiW S W ell k) (periodicLatticeShift b.1 b.2)|
      ≤ (2 * (ell : ℝ) ^ 2 * Real.log ell / W) / (ell : ℝ) ^ stratG (geomOf ell k S) (periodicLatticeShift b.1 b.2) := by
  have h := psi_bond hS hW hell hR hM hWR b
  simp only [Pi.neg_apply]
  rw [show -psiW S W ell k b.1 - -psiW S W ell k (periodicLatticeShift b.1 b.2)
      = -(psiW S W ell k b.1 - psiW S W ell k (periodicLatticeShift b.1 b.2)) by ring, abs_neg]
  exact h

/-- the block condition of `hatQ_comm` for `ψ`. -/
theorem psi_block (q : QIdx (geomOf ell k S)) (x : PeriodicLatticeSite Lf) (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    |psiW S W ell k (yq q) - psiW S W ell k x| ≤ 3 * (ell : ℝ) * Real.log ell / W := by
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  set j := jq q
  have hj : j ≤ k := by have := jq_le q; exact this
  have hy : yq q ∈ (geomOf ell k S).Lam j := yq_mem q
  have hyy : yq q ∈ blockOf (yq q) (ell ^ j) := by
    rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow j ell hell0; omega⟩
  have hsx : AdalyFormal.M1.strat S k x = j := by rw [strat_eq_stratG hell0 hS]; exact stratG_eq hP hj hy hx
  have hsy : AdalyFormal.M1.strat S k (yq q) = j := by rw [strat_eq_stratG hell0 hS]; exact stratG_eq hP hj hy hyy
  have hosc := psiW_osc hS hW (by omega) hWR hsy hsx
  have hd := pdist_block_le hx
  have hlog : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega))
  refine hosc.trans ?_
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hellr : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hcap := capW_pos hW (show 1 ≤ ell by omega) (j - 1)
  -- pdist / cap ≤ 3 ℓ / W
  have hfrac : (pdist (yq q) x : ℝ) / capW W ell (j - 1) ≤ 3 * (ell : ℝ) / W := by
    rw [div_le_div_iff₀ hcap (by linarith)]
    unfold capW
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · have : pdist (yq q) x = 0 := by rw [h0] at hd; simpa using hd
      rw [this]; simp; positivity
    · have hd' : (pdist (yq q) x : ℝ) ≤ 3 * ((ell : ℝ) ^ j - 1) := by
        have : pdist (yq q) x ≤ 3 * (ell ^ j - 1) := hd
        have h1 : 1 ≤ ell ^ j := Nat.one_le_pow _ _ hell0
        have : ((3 * (ell ^ j - 1) : ℕ) : ℝ) = 3 * ((ell : ℝ) ^ j - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub h1]; push_cast; ring
        calc (pdist (yq q) x : ℝ) ≤ ((3 * (ell ^ j - 1) : ℕ) : ℝ) := by exact_mod_cast hd
          _ = _ := this
      have hp : (ell : ℝ) ^ j = (ell : ℝ) * (ell : ℝ) ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpj : (0 : ℝ) < (ell : ℝ) ^ (j - 1) := by positivity
      rw [hp] at hd'
      nlinarith
  calc Real.log ell * ((pdist (yq q) x : ℝ) / capW W ell (j - 1)) ≤ Real.log ell * (3 * (ell : ℝ) / W) :=
        mul_le_mul_of_nonneg_left hfrac hlog
    _ = 3 * (ell : ℝ) * Real.log ell / W := by ring

theorem psi_block_neg (q : QIdx (geomOf ell k S)) (x : PeriodicLatticeSite Lf) (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    |(-psiW S W ell k) (yq q) - (-psiW S W ell k) x| ≤ 3 * (ell : ℝ) * Real.log ell / W := by
  simp only [Pi.neg_apply]
  rw [show -psiW S W ell k (yq q) - -psiW S W ell k x = -(psiW S W ell k (yq q) - psiW S W ell k x) by ring, abs_neg]
  exact psi_block hS hW hell hR hM hWR q x hx

theorem theta_nonneg : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := by
  have : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega))
  positivity

theorem delta0_nonneg : 0 ≤ 3 * (ell : ℝ) * Real.log ell / W := by
  have : 0 ≤ Real.log ell := Real.log_nonneg (by exact_mod_cast (show 1 ≤ ell by omega))
  positivity

/-- **the four hatted commutator bounds at `e^{±ψ}`** (operator norm). -/
theorem psi_hD (U : Cfg Lf) :
    ‖cjp (siteWP (psiW S W ell k)) (bondWP (psiW S W ell k)) (Dh (geomOf ell k S) U) - Dh (geomOf ell k S) U‖
        ≤ Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) ∧
      ‖cjm (siteWP (psiW S W ell k)) (bondWP (psiW S W ell k)) (Dh (geomOf ell k S) U) - Dh (geomOf ell k S) U‖
        ≤ Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) := by
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hθ := theta_nonneg hS hW hell hR hM hWR
  have hc : 0 ≤ Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) := by
    have : 0 ≤ Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1 := by linarith [Real.add_one_le_exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W)]
    positivity
  constructor
  · exact opnorm_le_of _ _ hc (fun f => hatD_comm hP hell0 U _ _ hθ (fun b _ => psi_bond hS hW hell hR hM hWR b) f)
  · rw [cjm_site_bond]
    exact opnorm_le_of _ _ hc (fun f => hatD_comm hP hell0 U _ _ hθ (fun b _ => psi_bond_neg hS hW hell hR hM hWR b) f)

theorem psi_hQ (U : Cfg Lf) (a : ℝ) (ha : 0 < a) :
    ‖cjp (siteWP (psiW S W ell k)) (ypWP (geomOf ell k S) (psiW S W ell k)) (Qh (geomOf ell k S) U a)
        - Qh (geomOf ell k S) U a‖ ≤ Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1) ∧
      ‖cjm (siteWP (psiW S W ell k)) (ypWP (geomOf ell k S) (psiW S W ell k)) (Qh (geomOf ell k S) U a)
        - Qh (geomOf ell k S) U a‖ ≤ Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1) := by
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hδ := delta0_nonneg hS hW hell hR hM hWR
  have hc : 0 ≤ Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1) := by
    have : 0 ≤ Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1 := by linarith [Real.add_one_le_exp (3 * (ell : ℝ) * Real.log ell / W)]
    positivity
  constructor
  · exact opnorm_le_of _ _ hc (fun f => hatQ_comm hP hell U a ha _ _ hδ (fun q x hx => psi_block hS hW hell hR hM hWR q x hx) f)
  · rw [cjm_site_yp]
    exact opnorm_le_of _ _ hc (fun f => hatQ_comm hP hell U a ha _ _ hδ (fun q x hx => psi_block_neg hS hW hell hR hM hWR q x hx) f)

end psi

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.cjm_site_bond
#print axioms AdalyFormal.M1IMS.cjm_site_yp
#print axioms AdalyFormal.M1IMS.psi_bond
#print axioms AdalyFormal.M1IMS.psi_bond_neg
#print axioms AdalyFormal.M1IMS.pdist_block_le
#print axioms AdalyFormal.M1IMS.psi_block
#print axioms AdalyFormal.M1IMS.psi_block_neg
#print axioms AdalyFormal.M1IMS.theta_nonneg
#print axioms AdalyFormal.M1IMS.delta0_nonneg
#print axioms AdalyFormal.M1IMS.psi_hD
#print axioms AdalyFormal.M1IMS.psi_hQ
