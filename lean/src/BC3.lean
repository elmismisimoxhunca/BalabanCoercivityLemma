import BC2
import BC1
import NJ11bNum
import NJ13bReg

/-!
# BC3 -- ONE LEVEL of the bond-composite drift in the volume-free `L²` norm

For the genuine composite jets `Y_j = D(qCompX_j)(0) a` (`QlinCompX`) at the tower background `bg` and at the FLAT
tower `bg1` (`bg1 j = 1`), with `nrm m Z = ‖(suOf (Z (c.1.1,c.2)))_c‖_{ℓ²(m-aligned bonds)}`:

  F:  nrm_{j+1}(Y_{j+1}^U)       ≤ (r + θ) nrm_j(Y_j^U),
  G:  nrm_{j+1}(Y_{j+1}^U - Y_{j+1}^1) ≤ r  nrm_j(Y_j^U - Y_j^1) + θ nrm_j(Y_j^U),

`r = sqrt(1/ell)`, `θ = ell (√192 ell ε + √240 κ(ε))`, `κ = e2Majorant(rhoOf ell ε)`; `ε` bounds `‖bg_j(e)-1‖_F` on the
`ell^j`-aligned bonds.  Pieces: NJE8 (`level_jet_sub_T1_l2`), NJ20c (`T1_drift_l2`), BC2 (`T1_flat_l2`, `sum_embE`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2 (XS QlinCompX RegTower)
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L Lq : PeriodicLatticeExtent}

/-! ## the `ℓ²` norm of an su(2)-valued function -/

def nr {ι : Type*} [Fintype ι] (w : ι → SuTwo) : ℝ := ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : ι => SuTwo))‖

theorem nr_nonneg {ι : Type*} [Fintype ι] (w : ι → SuTwo) : 0 ≤ nr w := norm_nonneg _

theorem nr_sq {ι : Type*} [Fintype ι] (w : ι → SuTwo) : nr w ^ 2 = ∑ i, ‖w i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

theorem nr_add_le {ι : Type*} [Fintype ι] (w1 w2 : ι → SuTwo) : nr (w1 + w2) ≤ nr w1 + nr w2 := by
  unfold nr
  have : (WithLp.toLp 2 (w1 + w2) : PiLp 2 (fun _ : ι => SuTwo))
      = WithLp.toLp 2 w1 + WithLp.toLp 2 w2 := rfl
  rw [this]
  exact norm_add_le _ _

theorem nr_le_of_sq {ι : Type*} [Fintype ι] (w : ι → SuTwo) {B : ℝ} (hB : 0 ≤ B)
    (h : ∑ i, ‖w i‖ ^ 2 ≤ B ^ 2) : nr w ≤ B :=
  le_of_sq_le' hB (by rw [nr_sq]; exact h)

theorem nr_eq_zero_of_sq {ι : Type*} [Fintype ι] (w : ι → SuTwo) (h : ∑ i, ‖w i‖ ^ 2 ≤ 0) : nr w = 0 :=
  le_antisymm (nr_le_of_sq w (le_refl _) (by simpa using h)) (nr_nonneg w)

/-! ## `suOf` is linear -/

theorem suOf_smul (r : ℝ) (v : Fin 3 → ℝ) : suOf (r • v) = r • suOf v := by
  apply Subtype.ext
  show AdalyFormal.IngredientFamilyR2.toM2 (r • v) = r • AdalyFormal.IngredientFamilyR2.toM2 v
  exact map_smul _ _ _

theorem suOf_sub (u v : Fin 3 → ℝ) : suOf (u - v) = suOf u - suOf v := by
  apply Subtype.ext
  show AdalyFormal.IngredientFamilyR2.toM2 (u - v)
    = AdalyFormal.IngredientFamilyR2.toM2 u - AdalyFormal.IngredientFamilyR2.toM2 v
  exact map_sub _ _ _

/-! ## level energies -/

/-- `ℓ²`-norm of the jet `Z` on the `m`-aligned bonds. -/
def nrm (m : ℕ) (Z : XS L) : ℝ := nr (fun c : CoarseBond L m => suOf (Z (c.1.1, c.2)))

theorem nrm_sq (m : ℕ) (Z : XS L) : nrm m Z ^ 2 = ∑ c : CoarseBond L m, ‖suOf (Z (c.1.1, c.2))‖ ^ 2 :=
  nr_sq _

theorem nrm_nonneg (m : ℕ) (Z : XS L) : 0 ≤ nrm m Z := nr_nonneg _

/-- `r = ell^{-1/2}`. -/
def rr (ell : ℕ) : ℝ := Real.sqrt (1 / (ell : ℝ))

/-- `θ(ε) = ell (√192 ell ε + √240 κ)`. -/
def thetaOf (ell : ℕ) (ε : ℝ) : ℝ :=
  (ell : ℝ) * (Real.sqrt 192 * ((ell : ℝ) * ε) + Real.sqrt 240 * e2Majorant (rhoOf ell ε))

theorem ell_sqrt_cube (ell : ℕ) (hell : 0 < ell) : (ell : ℝ) * Real.sqrt (1 / (ell : ℝ) ^ 3) = rr ell := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  unfold rr
  refine le_antisymm (le_of_sq_le' (Real.sqrt_nonneg _) ?_) (le_of_sq_le' (by positivity) ?_)
  · rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    apply le_of_eq; field_simp
  · rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    apply le_of_eq; field_simp

theorem rr_nonneg (ell : ℕ) : 0 ≤ rr ell := Real.sqrt_nonneg _

theorem thetaOf_nonneg (ell : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : 0 ≤ thetaOf ell ε := by
  unfold thetaOf
  have : 0 ≤ e2Majorant (rhoOf ell ε) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  positivity

/-- (copy of nonflat-jet `e2Majorant_numeric`, NJ19Num; that module's import closure contains the R2 `R2Ops2`
which clashes with the fork's `ZR2Ops2` used by the slice chain, so it cannot be imported here.) -/
theorem e2Majorant_numeric_bc {ell : ℕ} (hell : 0 < ell) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hle : ε0 ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    e2Majorant (rhoOf ell ε0) ≤ 12 * (8 * ell * (6 / 5 * ε0)) := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hρ := rhoOf_le (ell := ell) ε0 hε0
  have hρ0 : 0 ≤ rhoOf ell ε0 := by unfold rhoOf; positivity
  have hk : ε0 * (ell : ℝ) ^ 4 ≤ 1 / 1000 := by
    have hpos : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_right hle hpos.le
    calc _ ≤ 1 / (1000 * (ell : ℝ) ^ 4) * (ell : ℝ) ^ 4 := this
      _ = 1 / 1000 := by field_simp
  have h4 : (ell : ℝ) ≤ (ell : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ) ^ 2 - 1)]
  have hsmall10 : rhoOf ell ε0 ≤ 1 / 10 := by
    have : ell * ε0 ≤ 1 / 1000 := by nlinarith [hk, mul_le_mul_of_nonneg_right h4 hε0]
    nlinarith [hρ]
  exact le_trans (e2Majorant_le_twelve hρ0 hsmall10) (by nlinarith [hρ])

/-- (local copy of nonflat-jet `regTower_of_small`, NJ14Final, via NJ13bReg's `regBg_of_small`; same R2-clash reason.) -/
theorem regTower_of_small_bc {ell : ℕ} (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (J : ℕ) (ε : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j) (hV : ∀ j, j < J → ∀ e, frobNorm ((bg j e : M2) - 1) ≤ ε j)
    (hr : ∀ j, j < J → Real.pi / 2 * ((SmallnessBridge.Assemble.loopFactorBound ell : ℝ) * ε j) < r0) :
    RegTower ell bg J := by
  intro j hj
  exact regBg_of_small (pow_pos hell j) (bg j) (ε j) (hε j) (hV j hj) (hr j hj)

/-- at the flat background the (124) correction is zero (`ε = 0`). -/
theorem e2Majorant_rhoOf_zero {ell : ℕ} (hell : 0 < ell) : e2Majorant (rhoOf ell 0) = 0 := by
  have h := e2Majorant_numeric_bc hell 0 le_rfl (by positivity)
  have h0 : 0 ≤ e2Majorant (rhoOf ell 0) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  simp at h
  linarith

theorem frob_trivial_sub_one (L : PeriodicLatticeExtent) (e : PeriodicLatticeEdge L) :
    frobNorm (((trivialU L e : SU2) : M2) - 1) = 0 := by
  have : ((trivialU L e : SU2) : M2) = 1 := rfl
  rw [this, sub_self]
  exact AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero

section step
variable {s : ℕ}

theorem eq_of_sq_eq' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y :=
  le_antisymm (le_of_sq_le' hy h.le) (le_of_sq_le' hx h.ge)

theorem step_bounds (ell : ℕ) (bg bg1 : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) (hreg1 : RegTower ell bg1 J) (j : ℕ) (hj : j < J)
    (hs : ∀ μ, L μ + 1 = ell ^ j * (Lq μ + 1)) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (Lq μ + 1)) (ε : ℝ) (hε : 0 ≤ ε)
    (hV : ∀ e, frobNorm (((resV hs (bg j)) e : M2) - 1) ≤ ε) (hsmall : rhoOf ell ε < Real.pi / 2)
    (hbg1 : bg1 j = trivialU L) (a : XS L) :
    nrm (ell ^ j * ell) (QlinCompX ell bg (j + 1) a)
        ≤ (rr ell + thetaOf ell ε) * nrm (ell ^ j * 1) (QlinCompX ell bg j a)
    ∧ nrm (ell ^ j * ell) (QlinCompX ell bg (j + 1) a - QlinCompX ell bg1 (j + 1) a)
        ≤ rr ell * nrm (ell ^ j * 1) (QlinCompX ell bg j a - QlinCompX ell bg1 j a)
          + thetaOf ell ε * nrm (ell ^ j * 1) (QlinCompX ell bg j a) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hell0 : (ell : ℝ) ≠ 0 := hellR.ne'
  have hκ0 : 0 ≤ e2Majorant (rhoOf ell ε) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  set YU := QlinCompX ell bg j a with hYU
  set YU' := QlinCompX ell bg (j + 1) a with hYU'
  set Y1 := QlinCompX ell bg1 j a with hY1
  set Y1' := QlinCompX ell bg1 (j + 1) a with hY1'
  -- the unit-bond fields
  set AU : CoarseBond Lq 1 → SuTwo := fun b => suOf (resA hs YU (b.1.1, b.2)) with hAU
  set A1 : CoarseBond Lq 1 → SuTwo := fun b => suOf (resA hs Y1 (b.1.1, b.2)) with hA1
  -- energies
  have hEU : ∑ e : PeriodicLatticeEdge Lq, ‖suOf (resA hs YU e)‖ ^ 2 = nrm (ell ^ j * 1) YU ^ 2 := by
    rw [nrm_sq]; exact sum_embE_edge hs (fun b => ‖suOf (YU b)‖ ^ 2)
  have hEG : ∑ e : PeriodicLatticeEdge Lq, ‖suOf (resA hs (YU - Y1) e)‖ ^ 2
      = nrm (ell ^ j * 1) (YU - Y1) ^ 2 := by
    rw [nrm_sq]; exact sum_embE_edge hs (fun b => ‖suOf ((YU - Y1) b)‖ ^ 2)
  have hlU : l1 (gA AU) = ∑ e : PeriodicLatticeEdge Lq, ‖suOf (resA hs YU e)‖ ^ 2 := rfl
  have hAUA1 : (fun b : CoarseBond Lq 1 => AU b - A1 b)
      = fun b => suOf (resA hs (YU - Y1) (b.1.1, b.2)) := by
    funext b
    simp only [hAU, hA1]
    rw [← suOf_sub]; rfl
  have hlG : l1 (gA (fun b : CoarseBond Lq 1 => AU b - A1 b))
      = ∑ e : PeriodicLatticeEdge Lq, ‖suOf (resA hs (YU - Y1) e)‖ ^ 2 := by
    rw [hAUA1]; rfl
  -- the vectors on `CoarseBond Lq ell`
  set uU : CoarseBond Lq ell → SuTwo := fun c => suOf ((ell : ℝ)⁻¹ • YU' (embE hs (c.1.1, c.2))) with huU
  set u1 : CoarseBond Lq ell → SuTwo := fun c => suOf ((ell : ℝ)⁻¹ • Y1' (embE hs (c.1.1, c.2))) with hu1
  set T1 : (PeriodicLinkConfiguration SU2 Lq) → (CoarseBond Lq 1 → SuTwo) → CoarseBond Lq ell → SuTwo :=
    fun V B c => unitToCoarseCov 1 ell V B (cbEquiv ell c) with hT1
  -- jet remainders (NJE8)
  have hRU := level_jet_sub_T1_l2 ell bg J hreg j hj hs hell hdvd ε hε hV hsmall a
  have hV1 : ∀ e, frobNorm (((resV hs (bg1 j)) e : M2) - 1) ≤ 0 := by
    intro e
    rw [hbg1]
    exact le_of_eq (frob_trivial_sub_one Lq e)
  have hR1 := level_jet_sub_T1_l2 ell bg1 J hreg1 j hj hs hell hdvd 0 le_rfl hV1
    (by unfold rhoOf; simp; exact Real.pi_pos) a
  rw [e2Majorant_rhoOf_zero hell] at hR1
  have hδU : nr (fun c => uU c - T1 (resV hs (bg j)) AU c) ≤ Real.sqrt 240 * e2Majorant (rhoOf ell ε)
      * nrm (ell ^ j * 1) YU := by
    refine nr_le_of_sq _ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hκ0) (nrm_nonneg _ _)) ?_
    have e : (Real.sqrt 240 * e2Majorant (rhoOf ell ε) * nrm (ell ^ j * 1) YU) ^ 2
        = Real.sqrt 240 ^ 2 * e2Majorant (rhoOf ell ε) ^ 2 * nrm (ell ^ j * 1) YU ^ 2 := by ring
    rw [e, Real.sq_sqrt (by norm_num), ← hEU]
    exact hRU
  have hδ1 : nr (fun c => u1 c - T1 (resV hs (bg1 j)) A1 c) = 0 := by
    refine nr_eq_zero_of_sq _ ?_
    refine le_trans hR1 (le_of_eq ?_)
    ring
  -- flat T1 on bg1's restriction is the trivial background
  have hres1 : resV hs (bg1 j) = trivialU Lq := by rw [hbg1]; rfl
  -- T1 estimates
  have hT1flat : ∀ B : CoarseBond Lq 1 → SuTwo,
      nr (T1 (trivialU Lq) B) ≤ Real.sqrt (1 / (ell : ℝ) ^ 3) * Real.sqrt (l1 (gA B)) := by
    intro B
    have hl : 0 ≤ l1 (gA B) := Finset.sum_nonneg fun e _ => gA_nonneg B e
    refine nr_le_of_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hl]
    have := T1_flat_l2 hell B
    have heq := Equiv.sum_comp (cbEquiv ell) (fun c' : CoarseBond Lq (1 * ell) =>
      ‖unitToCoarseCov 1 ell (trivialU Lq) B c'‖ ^ 2)
    exact (le_of_eq heq).trans this
  have hT1drift : nr (fun c => T1 (resV hs (bg j)) AU c - T1 (trivialU Lq) AU c)
      ≤ Real.sqrt 192 * ((ell : ℝ) * ε) * nrm (ell ^ j * 1) YU := by
    refine nr_le_of_sq _ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (nrm_nonneg _ _)) ?_
    have e : (Real.sqrt 192 * ((ell : ℝ) * ε) * nrm (ell ^ j * 1) YU) ^ 2
        = Real.sqrt 192 ^ 2 * ((ell : ℝ) * ε) ^ 2 * nrm (ell ^ j * 1) YU ^ 2 := by ring
    rw [e, Real.sq_sqrt (by norm_num), ← hEU, ← hlU]
    have := T1_drift_l2 hell (resV hs (bg j)) ε hε hV AU
    have heq := Equiv.sum_comp (cbEquiv ell) (fun c' : CoarseBond Lq (1 * ell) =>
      ‖unitToCoarseCov 1 ell (resV hs (bg j)) AU c' - unitToCoarseCov 1 ell (trivialU Lq) AU c'‖ ^ 2)
    refine (le_of_eq heq).trans (this.trans (le_of_eq ?_))
    ring
  -- relate uU, u1 to the level energies
  have hsum1 : ∑ c : CoarseBond Lq ell, ‖suOf (YU' (embE hs (c.1.1, c.2)))‖ ^ 2
      = nrm (ell ^ j * ell) YU' ^ 2 := by
    rw [nrm_sq]; exact sum_embE hs ell (fun b => ‖suOf (YU' b)‖ ^ 2)
  have hsum2 : ∑ c : CoarseBond Lq ell, ‖suOf ((YU' - Y1') (embE hs (c.1.1, c.2)))‖ ^ 2
      = nrm (ell ^ j * ell) (YU' - Y1') ^ 2 := by
    rw [nrm_sq]; exact sum_embE hs ell (fun b => ‖suOf ((YU' - Y1') b)‖ ^ 2)
  have hinvnn : (0 : ℝ) ≤ (ell : ℝ)⁻¹ := inv_nonneg.2 hellR.le
  have hnuU : nr uU = (ell : ℝ)⁻¹ * nrm (ell ^ j * ell) YU' := by
    refine eq_of_sq_eq' (nr_nonneg _) (mul_nonneg hinvnn (nrm_nonneg _ _)) ?_
    rw [nr_sq, mul_pow, ← hsum1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [huU]
    rw [suOf_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have huG : ∀ c, uU c - u1 c = suOf ((ell : ℝ)⁻¹ • (YU' - Y1') (embE hs (c.1.1, c.2))) := by
    intro c
    simp only [huU, hu1]
    rw [← suOf_sub, ← smul_sub]
    rfl
  have hnuG : nr (fun c => uU c - u1 c) = (ell : ℝ)⁻¹ * nrm (ell ^ j * ell) (YU' - Y1') := by
    refine eq_of_sq_eq' (nr_nonneg _) (mul_nonneg hinvnn (nrm_nonneg _ _)) ?_
    rw [nr_sq, mul_pow, ← hsum2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [huG c, suOf_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hinv : ∀ x : ℝ, (ell : ℝ) * ((ell : ℝ)⁻¹ * x) = x := fun x => by field_simp
  constructor
  · -- F
    have hdec : uU = T1 (trivialU Lq) AU + (fun c => T1 (resV hs (bg j)) AU c - T1 (trivialU Lq) AU c)
        + (fun c => uU c - T1 (resV hs (bg j)) AU c) := by
      funext c; simp only [Pi.add_apply]; abel
    have h1 : nr uU ≤ nr (T1 (trivialU Lq) AU) + nr (fun c => T1 (resV hs (bg j)) AU c - T1 (trivialU Lq) AU c)
        + nr (fun c => uU c - T1 (resV hs (bg j)) AU c) := by
      conv_lhs => rw [hdec]
      exact (nr_add_le _ _).trans (add_le_add (nr_add_le _ _) le_rfl)
    have h2 := hT1flat AU
    rw [hlU, hEU, Real.sqrt_sq (nrm_nonneg _ _)] at h2
    have h3 : (ell : ℝ)⁻¹ * nrm (ell ^ j * ell) YU' ≤
        Real.sqrt (1 / (ell : ℝ) ^ 3) * nrm (ell ^ j * 1) YU
        + Real.sqrt 192 * ((ell : ℝ) * ε) * nrm (ell ^ j * 1) YU
        + Real.sqrt 240 * e2Majorant (rhoOf ell ε) * nrm (ell ^ j * 1) YU := by
      rw [← hnuU]; linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hellR.le
    rw [hinv] at h4
    refine h4.trans (le_of_eq ?_)
    rw [thetaOf, ← ell_sqrt_cube ell hell]
    ring
  · -- G
    have hdecG : (fun c => uU c - u1 c)
        = (fun c => T1 (resV hs (bg j)) AU c - T1 (trivialU Lq) AU c)
          + T1 (trivialU Lq) (fun b => AU b - A1 b)
          + (fun c => uU c - T1 (resV hs (bg j)) AU c)
          - (fun c => u1 c - T1 (resV hs (bg1 j)) A1 c) := by
      funext c
      have hlin : unitToCoarseCov 1 ell (trivialU Lq) (fun b => AU b - A1 b) (cbEquiv ell c)
          = unitToCoarseCov 1 ell (trivialU Lq) AU (cbEquiv ell c)
            - unitToCoarseCov 1 ell (trivialU Lq) A1 (cbEquiv ell c) := by
        have := map_sub (AdalyFormal.Balaban.TowerLawCov.unitToCoarseCovLM 1 ell (trivialU Lq)) AU A1
        exact congrFun this _
      simp only [Pi.add_apply, Pi.sub_apply, hT1, hlin, hres1]
      abel
    have hsub : ∀ (w1 w2 : CoarseBond Lq ell → SuTwo), nr (w1 - w2) ≤ nr w1 + nr w2 := by
      intro w1 w2
      have hneg : nr (-w2) = nr w2 := by
        unfold nr
        have : (WithLp.toLp 2 (-w2) : PiLp 2 (fun _ : CoarseBond Lq ell => SuTwo))
            = -(WithLp.toLp 2 w2) := rfl
        rw [this, norm_neg]
      rw [sub_eq_add_neg]
      exact (nr_add_le _ _).trans (le_of_eq (by rw [hneg]))
    have h1 : nr (fun c => uU c - u1 c) ≤
        nr (fun c => T1 (resV hs (bg j)) AU c - T1 (trivialU Lq) AU c)
        + nr (T1 (trivialU Lq) (fun b => AU b - A1 b))
        + nr (fun c => uU c - T1 (resV hs (bg j)) AU c)
        + nr (fun c => u1 c - T1 (resV hs (bg1 j)) A1 c) := by
      rw [hdecG]
      exact (hsub _ _).trans (add_le_add ((nr_add_le _ _).trans (add_le_add (nr_add_le _ _) le_rfl)) le_rfl)
    have h2 := hT1flat (fun b => AU b - A1 b)
    rw [hlG, hEG, Real.sqrt_sq (nrm_nonneg _ _)] at h2
    have h3 : (ell : ℝ)⁻¹ * nrm (ell ^ j * ell) (YU' - Y1') ≤
        Real.sqrt 192 * ((ell : ℝ) * ε) * nrm (ell ^ j * 1) YU
        + Real.sqrt (1 / (ell : ℝ) ^ 3) * nrm (ell ^ j * 1) (YU - Y1)
        + Real.sqrt 240 * e2Majorant (rhoOf ell ε) * nrm (ell ^ j * 1) YU := by
      rw [← hnuG]; rw [hδ1] at h1; linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hellR.le
    rw [hinv] at h4
    refine h4.trans (le_of_eq ?_)
    rw [thetaOf, ← ell_sqrt_cube ell hell]
    ring

end step

#print axioms nr_add_le
#print axioms ell_sqrt_cube
#print axioms e2Majorant_rhoOf_zero
#print axioms step_bounds

end AdalyFormal.BondComposite
