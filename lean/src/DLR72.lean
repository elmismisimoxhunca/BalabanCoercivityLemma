import DLR71
import BC6

/-!
# DL72 -- **the composite second jet in `ℓ¹`** on the full tower: `Σ_{c ℓ^k-aligned} ‖C_k(a)(c)‖ ≤ C·ℓ^{-k}·‖a‖²`

Recursion (`C2CompX_succ`): `C_{j+1}(a) = QlinStep_j(C_j a) + C2Step_j(QlinCompX_j a)`, `C_0 = 0` (`C2CompX_zero`).  With
`S_j = Σ_{ℓ^j-aligned} ‖suOf (C_j a)‖`, `T_j = nrm(ℓ^j)(QlinCompX_j a)²`:
  `S_{j+1} ≤ A_j S_j + K2s ℓ · T_j`  (DL71 `Qlin_l1`, DL69 `C2Step_l1`),   `T_j ≤ ℓ^{-j} e^{2Σθ/rr} ‖a‖²`  (BC5 `tower_FG`).
If `A_j ≤ θ/ℓ` (`θ < 1`) then by induction `S_j ≤ K2s·X·ℓ/(1−θ)·ℓ^{-j}` (`X = e^{2Σθ/rr}‖a‖²`): **`C2Comp_l1`**.
Background inputs: `RegTower`, the tower class `TowerClass ε` (links at the `ℓ^j`-aligned bonds within `ε_j` of `1`),
`rhoOf ℓ ε_j < π/2`, `8ℓε_j ≤ 1/16` (loops, `loop_dev`), and the contraction condition `ℓ^{-2} + 1536ℓκ(ε_j) ≤ θ/ℓ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

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
  toM2 toM2_mem bgTower)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (suOf embE embS embS_val resV rhoOf)
open AdalyFormal.BondComposite (nrm nrm_sq nrm_nonneg rr thetaOf thetaOf_nonneg TowerClass hsLq hdvdLq hdvd_scaleUp
  tower_FG)
open EstimatesLayer.E1E3 (e2Majorant)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-! ## deviations of products of `SU(2)` links -/

theorem dev_mul (g h : SU2) : frobNorm (((g * h : SU2) : Mt) - 1) ≤ frobNorm ((g : Mt) - 1) + frobNorm ((h : Mt) - 1) := by
  rw [coe_mul]
  have e : (g : Mt) * (h : Mt) - 1 = ((g : Mt) - 1) * (h : Mt) + ((h : Mt) - 1) := by
    simp only [sub_mul, one_mul]; abel
  rw [e]; refine (fN_add _ _).trans ?_
  rw [fN_mul_su2]

theorem dev_inv (g : SU2) : frobNorm (((g⁻¹ : SU2) : Mt) - 1) = frobNorm ((g : Mt) - 1) := by
  rw [coe_inv]
  have e : (g : Mt)ᴴ - 1 = ((g : Mt) - 1)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [e, fN_conjT]

theorem hol_dev (s : ℕ) (V : PeriodicLinkConfiguration SU2 L) (ε : ℝ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), (∀ e, OnPath s y p e → frobNorm (((V e : SU2) : Mt) - 1) ≤ ε) →
      frobNorm (((coarsePathHolonomy s V y p : SU2) : Mt) - 1) ≤ p.length * ε := by
  intro p
  induction p with
  | nil => intro y _; simp [coarsePathHolonomy, coe_one, fN_zero]
  | cons μ rest ih =>
      intro y hV
      have h1 := hV (y, μ) (Or.inl rfl)
      have h2 := ih (coarseShift y s μ) (fun e he => hV e (Or.inr he))
      have e1 : coarsePathHolonomy s V y (μ :: rest) = V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest := rfl
      rw [e1]
      refine (dev_mul _ _).trans ?_
      simp only [List.length_cons]; push_cast; linarith

theorem dev4 (A B C D : SU2) :
    frobNorm (((A * B * C⁻¹ * D⁻¹ : SU2) : Mt) - 1)
      ≤ frobNorm ((A : Mt) - 1) + frobNorm ((B : Mt) - 1) + frobNorm ((C : Mt) - 1) + frobNorm ((D : Mt) - 1) := by
  have h1 := dev_mul (A * B * C⁻¹) D⁻¹
  have h2 := dev_mul (A * B) C⁻¹
  have h3 := dev_mul A B
  rw [dev_inv] at h1 h2
  linarith

theorem loopVar_eq (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    loopVar s ell V c x = coarsePathHolonomy s V c.1 (coarseGammaPath s c.1 x)
      * coarsePathHolonomy s V x (List.replicate ell c.2)
      * (coarsePathHolonomy s V (cPlusS s ell c) (coarseGammaPath s c.1 x))⁻¹
      * (coarsePathHolonomy s V c.1 (List.replicate ell c.2))⁻¹ := rfl

theorem loop_dev (s ell : ℕ) (hs : 0 < s) (hL : ∀ ν, s ∣ L ν + 1) (V : PeriodicLinkConfiguration SU2 L) (ε : ℝ)
    (hε : 0 ≤ ε) (hV : ∀ e : PeriodicLatticeEdge L, (∀ ν, s ∣ (e.1 ν).val) → frobNorm (((V e : SU2) : Mt) - 1) ≤ ε)
    (c : PeriodicLatticeEdge L) (hc : ∀ ν, s ∣ (c.1 ν).val) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 s ell) (hell : 0 < ell) :
    frobNorm (((loopVar s ell V c x : SU2) : Mt) - 1) ≤ 8 * ell * ε := by
  have hlen := gamma_len_le s ell hs c.1 x hx
  have hG : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
    have h3 : ((3 * (ell - 1) : ℕ) : ℝ) = 3 * ((ell : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; norm_num
    rw [← h3]; exact_mod_cast hlen
  have hx' := block_dvd s ell c.1 x hc hx
  have hp := cPlusS_dvd s ell hL c hc
  have d1 := hol_dev s V ε (coarseGammaPath s c.1 x) c.1 (fun e he => hV e (onPath_dvd s hL _ _ e hc he))
  have d2 := hol_dev s V ε (List.replicate ell c.2) x (fun e he => hV e (onPath_dvd s hL _ _ e hx' he))
  have d3 := hol_dev s V ε (coarseGammaPath s c.1 x) (cPlusS s ell c) (fun e he => hV e (onPath_dvd s hL _ _ e hp he))
  have d4 := hol_dev s V ε (List.replicate ell c.2) c.1 (fun e he => hV e (onPath_dvd s hL _ _ e hc he))
  rw [List.length_replicate] at d2 d4
  rw [loopVar_eq]
  have h4 := dev4 (coarsePathHolonomy s V c.1 (coarseGammaPath s c.1 x))
    (coarsePathHolonomy s V x (List.replicate ell c.2))
    (coarsePathHolonomy s V (cPlusS s ell c) (coarseGammaPath s c.1 x))
    (coarsePathHolonomy s V c.1 (List.replicate ell c.2))
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hGe := mul_le_mul_of_nonneg_right hG hε
  have h8 : (3 * ((ell : ℝ) - 1)) * ε = 3 * ((ell : ℝ) * ε) - 3 * ε := by ring
  have h9 : 8 * (ell : ℝ) * ε = 8 * ((ell : ℝ) * ε) := by ring
  rw [h8] at hGe
  rw [h9]
  linarith

/-! ## level 0 and linearity of `suOf` -/

theorem C2CompX_zero (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (a : XS L) : C2CompX ell bg 0 a = 0 := by
  have h : fderiv ℝ (qCompX ell bg 0) = fun _ => ContinuousLinearMap.id ℝ (XS L) := by
    funext x; show fderiv ℝ id x = _; exact fderiv_id
  have h1 : fderiv ℝ (fderiv ℝ (qCompX ell bg 0)) 0 = 0 := by
    rw [h]; exact fderiv_const_apply _
  show (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qCompX ell bg 0)) 0 a a = 0
  rw [h1]; simp

theorem suOf_add (u v : Fin 3 → ℝ) : suOf (u + v) = suOf u + suOf v := by
  apply Subtype.ext
  show toM2 (u + v) = toM2 u + toM2 v
  exact map_add _ _ _

/-! ## the closed-form induction -/

theorem rec_closed (k : ℕ) (S T : ℕ → ℝ) (A K X ell θ : ℝ) (hell : 0 < ell) (hθ1 : θ < 1) (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hA0 : 0 ≤ A) (hA : A ≤ θ / ell) (h0 : S 0 = 0) (hS0 : ∀ j, 0 ≤ S j)
    (hS : ∀ j, j < k → S (j + 1) ≤ A * S j + K * T j) (hT : ∀ j, j < k → T j ≤ X * (1 / ell) ^ j) :
    ∀ j, j ≤ k → S j ≤ K * X * ell / (1 - θ) * (1 / ell) ^ j := by
  have h1θ : 0 < 1 - θ := by linarith
  have hBnn : ∀ j : ℕ, 0 ≤ K * X * ell / (1 - θ) * (1 / ell) ^ j := fun j =>
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hK hX) hell.le) h1θ.le) (pow_nonneg (by positivity) j)
  intro j
  induction j with
  | zero => intro _; rw [h0]; exact hBnn 0
  | succ j ih =>
      intro hj
      have hjk : j < k := by omega
      have hrec := hS j hjk
      have hih := ih hjk.le
      have hT' := hT j hjk
      set B := K * X * ell / (1 - θ) * (1 / ell) ^ j with hB
      have hB0 : 0 ≤ B := hBnn j
      have hp : (0 : ℝ) ≤ (1 / ell) ^ j := by positivity
      have t1 : A * S j ≤ (θ / ell) * B := mul_le_mul hA hih (hS0 j) (le_trans hA0 hA)
      have t2 : K * T j ≤ K * (X * (1 / ell) ^ j) := mul_le_mul_of_nonneg_left hT' hK
      have e : K * X * ell / (1 - θ) * (1 / ell) ^ (j + 1) = (θ / ell) * B + K * (X * (1 / ell) ^ j) := by
        rw [hB, pow_succ]; field_simp; ring
      rw [e]; linarith

#print axioms dev_mul
#print axioms hol_dev
#print axioms loop_dev
#print axioms C2CompX_zero
#print axioms rec_closed

end AdalyFormal.DLayer
