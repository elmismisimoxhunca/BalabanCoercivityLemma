import DLR72

/-!
# DL73 -- **the composite second jet in `ℓ¹`** on the full tower: `Σ_{c ℓ^k-aligned} ‖C_k(a)(c)‖ ≤ C·ℓ^{-k}·‖a‖²`

Recursion (`C2CompX_succ`): `C_{j+1}(a) = QlinStep_j(C_j a) + C2Step_j(QlinCompX_j a)`, `C_0 = 0` (`C2CompX_zero`).  With
`S_j = Σ_{ℓ^j-aligned} ‖suOf (C_j a)‖`, `T_j = nrm(ℓ^j)(QlinCompX_j a)²`:
  `S_{j+1} ≤ A_j S_j + K2s ℓ · T_j`  (DL71 `Qlin_l1`, DL69 `C2Step_l1`),   `T_j ≤ ℓ^{-j} e^{2Σθ/rr} ‖a‖²`  (BC5 `tower_FG`).
If `A_j ≤ θ/ℓ` (`θ < 1`) then by induction `S_j ≤ K2s·X·ℓ/(1−θ)·ℓ^{-j}` (`X = e^{2Σθ/rr}‖a‖²`): **`C2Comp_l1`**.
Background inputs: `RegTower`, the tower class `TowerClass ε` (links at the `ℓ^j`-aligned bonds within `ε_j` of `1`),
`rhoOf ℓ ε_j < π/2`, `8ℓε_j ≤ 1/16` (loops, `loop_dev`), and the contraction condition `ℓ^{-2} + 1536ℓκ(ε_j) ≤ θ/ℓ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq norm_sq_eq_half_frobSq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2NegOne coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar cPlusS)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.IngredientFamilyR2 (QlinStepX C2StepX QlinCompX C2CompX C2CompX_succ qCompX RegBg RegTower XS
  toM2 toM2_mem bgTower Cfg)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (suOf embE embS embS_val resV rhoOf)
open AdalyFormal.BondComposite (nrm nrm_sq nrm_nonneg rr thetaOf thetaOf_nonneg TowerClass hsLq hdvdLq hdvd_scaleUp
  tower_FG)
open EstimatesLayer.E1E3 (e2Majorant)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-! ## the composite second jet -/

theorem C2Comp_l1 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (ε : ℕ → ℝ) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (hloop : ∀ j, j < k → 8 * (ell : ℝ) * ε j ≤ 1 / 16)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hA : ∀ j, j < k → 1 / (ell : ℝ) ^ 2 + 1536 * ell * e2Majorant (rhoOf ell (ε j)) ≤ θ / ell)
    (a : XS (scaleUp ell k Lu)) :
    ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ k),
        ‖suOf (C2CompX ell (bgTower (GF ell k Lu) U) k a (c.1.1, c.2))‖
      ≤ K2s ell * (Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) * nrm 1 a) ^ 2 * ell / (1 - θ)
          * (1 / (ell : ℝ)) ^ k := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set SS := ∑ i ∈ Finset.range k, thetaOf ell (ε i) with hSS
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hrr : rr ell ^ 2 = 1 / (ell : ℝ) := by
    unfold AdalyFormal.BondComposite.rr; rw [Real.sq_sqrt (by positivity)]
  set S : ℕ → ℝ := fun j => ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ j), ‖suOf (C2CompX ell (bgTower (GF ell k Lu) U) j a (c.1.1, c.2))‖ with hSdef
  set T : ℕ → ℝ := fun j => nrm (ell ^ j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a) ^ 2 with hTdef
  have hS0 : ∀ j, 0 ≤ S j := fun j => Finset.sum_nonneg (fun c _ => norm_nonneg _)
  have h0 : S 0 = 0 := by
    simp only [hSdef, C2CompX_zero, Pi.zero_apply]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    have : suOf 0 = 0 := Subtype.ext (map_zero toM2)
    rw [this, norm_zero]
  -- the contraction factor, uniform
  set κmax : ℝ := (θ / ell - 1 / (ell : ℝ) ^ 2) / (1536 * ell) with hκmax
  -- per-level step
  have hstep : ∀ j, j < k → S (j + 1) ≤ (θ / ell) * S j + K2s ell * T j := by
    intro j hj
    have hs := hsLq ell k Lu hell j hj.le
    have hdq := hdvdLq ell k Lu hell j hj
    have hsj : 0 < ell ^ j := pow_pos hell j
    have hLj : ∀ ν, ell ^ j ∣ scaleUp ell k Lu ν + 1 := fun ν => hdvd_scaleUp ell k Lu hell j hj.le ν
    have hn : ∀ ν, ell ^ j * ell ∣ scaleUp ell k Lu ν + 1 := fun ν => by
      rw [← pow_succ]; exact hdvd_scaleUp ell k Lu hell (j + 1) hj ν
    have hVr : ∀ e : PeriodicLatticeEdge (scaleUp ell (k - j) Lu), frobNorm (((resV hs ((bgTower (GF ell k Lu) U) j)) e : M2) - 1) ≤ ε j := by
      intro e
      have hmem : embS hs e.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j) := by
        rw [mem_CoarseLattice]; intro μ; rw [embS_val]; exact Nat.mul_mod_right _ _
      exact hcl j hj _ hmem e.2
    have hValign : ∀ e : PeriodicLatticeEdge (scaleUp ell k Lu), (∀ ν, ell ^ j ∣ (e.1 ν).val) → frobNorm ((((bgTower (GF ell k Lu) U) j e : SU2) : Mt) - 1) ≤ ε j := by
      intro e he
      have hmem : e.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j) := mem_CoarseLattice.mpr (fun ν => Nat.mod_eq_zero_of_dvd (he ν))
      exact hcl j hj e.1 hmem e.2
    have hW : ∀ c : CoarseBond (scaleUp ell k Lu) (ell ^ j * ell), ∀ x ∈ stepBlockOf c.1.1 (ell ^ j) ell,
        frobNorm (((loopVar (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) (c.1.1, c.2) x : SU2) : Mt) - 1) ≤ 1 / 16 := by
      intro c x hx
      have hc : ∀ ν, ell ^ j ∣ ((c.1.1, c.2).1 ν).val := fun ν =>
        dvd_trans (dvd_mul_right _ _) (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp c.1.2 ν))
      exact (loop_dev (ell ^ j) ell hsj hLj ((bgTower (GF ell k Lu) U) j) (ε j) (hε0 j hj) hValign (c.1.1, c.2) hc x hx hell).trans
        (hloop j hj)
    have hreg_j : RegBg (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) := hreg j hj
    -- the recursion at the aligned bonds
    have hsplit : ∀ c : CoarseBond (scaleUp ell k Lu) (ell ^ (j + 1)),
        ‖suOf (C2CompX ell (bgTower (GF ell k Lu) U) (j + 1) a (c.1.1, c.2))‖
          ≤ ‖suOf (QlinStepX (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) (C2CompX ell (bgTower (GF ell k Lu) U) j a) (c.1.1, c.2))‖
            + ‖suOf (C2StepX (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a) (c.1.1, c.2))‖ := by
      intro c
      rw [C2CompX_succ ell (bgTower (GF ell k Lu) U) k hreg j hj a, Pi.add_apply, suOf_add]
      exact norm_add_le _ _
    have hQ := Qlin_l1 hs ell hell hdq ((bgTower (GF ell k Lu) U) j) hreg_j (ε j) (hε0 j hj) hVr (hsm j hj) (C2CompX ell (bgTower (GF ell k Lu) U) j a)
    have hC := C2Step_l1 (ell ^ j) ell hsj hell hn ((bgTower (GF ell k Lu) U) j) hreg_j hW (QlinCompX ell (bgTower (GF ell k Lu) U) j a)
    have hAj := hA j hj
    have hS_j0 := hS0 j
    calc S (j + 1) ≤ ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ (j + 1)),
          (‖suOf (QlinStepX (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) (C2CompX ell (bgTower (GF ell k Lu) U) j a) (c.1.1, c.2))‖
            + ‖suOf (C2StepX (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a) (c.1.1, c.2))‖) :=
          Finset.sum_le_sum (fun c _ => hsplit c)
      _ = ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ j * ell),
            ‖suOf (QlinStepX (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) (C2CompX ell (bgTower (GF ell k Lu) U) j a) (c.1.1, c.2))‖
          + ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ j * ell),
            ‖suOf (C2StepX (ell ^ j) ell ((bgTower (GF ell k Lu) U) j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a) (c.1.1, c.2))‖ := Finset.sum_add_distrib
      _ ≤ (1 / (ell : ℝ) ^ 2 + 1536 * ell * e2Majorant (rhoOf ell (ε j))) * S j
          + K2s ell * ∑ e : CoarseBond (scaleUp ell k Lu) (ell ^ j), ‖suOf (QlinCompX ell (bgTower (GF ell k Lu) U) j a (e.1.1, e.2))‖ ^ 2 :=
          add_le_add hQ hC
      _ ≤ (θ / ell) * S j + K2s ell * T j := by
          refine add_le_add (mul_le_mul_of_nonneg_right hAj hS_j0) (le_of_eq ?_)
          rw [hTdef]; simp only; rw [nrm_sq]
  -- T_j bound
  have hT : ∀ j, j < k → T j ≤ (Real.exp (SS / rr ell) * nrm 1 a) ^ 2 * (1 / (ell : ℝ)) ^ j := by
    intro j hj
    have hFG := (tower_FG ell k Lu hell U ε hreg hcl hε0 hsm a j hj.le).1
    have hSj : ∑ i ∈ Finset.range j, thetaOf ell (ε i) ≤ SS := by
      rw [hSS]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj.le)
        (fun i hi _ => thetaOf_nonneg ell _ (hε0 i (by have := Finset.mem_range.mp hi; omega)))
    have hexp : Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) ≤ Real.exp (SS / rr ell) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hSj hr.le)
    have hX := nrm_nonneg 1 a
    have h1 : nrm (ell ^ j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a) ≤ rr ell ^ j * (Real.exp (SS / rr ell) * nrm 1 a) := by
      refine hFG.trans ?_
      have : (rr ell) ^ j * Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) * nrm 1 a
          ≤ (rr ell) ^ j * Real.exp (SS / rr ell) * nrm 1 a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity)) hX
      linarith
    have h2 := pow_le_pow_left₀ (nrm_nonneg _ _) h1 2
    show nrm (ell ^ j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a) ^ 2 ≤ _
    refine h2.trans (le_of_eq ?_)
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul, hrr]; ring
  have hfin := rec_closed k S T (θ / ell) (K2s ell) ((Real.exp (SS / rr ell) * nrm 1 a) ^ 2) ell θ hellR hθ1
    (by unfold K2s; positivity) (by positivity) (by positivity) le_rfl h0 hS0 hstep hT k le_rfl
  refine hfin.trans (le_of_eq ?_)
  ring

#print axioms C2Comp_l1

end AdalyFormal.DLayer
