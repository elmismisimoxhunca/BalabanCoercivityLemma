import DQ1

/-!
# DQ2 -- the composite second jet in `ℓ¹` at an INTERMEDIATE depth `n`, from link / plaquette bounds at scale `α`

On the lattice `scaleUp ℓ n Lu'` (any `Lu'`, any `n`), for ANY configuration `V` with
  `dv(V b) ≤ α/ℓⁿ` (every link), `dv(plaquette) ≤ α/ℓ²ⁿ` (every plaquette), `2ℓⁿ < N_ρ` (torus),
and the k-free (indeed n-free) smallness `4·10⁶ ℓ² α ≤ 1`, `KUSmall ℓ ρ`, `ρ ≤ 1/(1000ℓ³)`,
`1536 ℓ² e2Majorant(rhoOf ℓ ρ) < 1 − 1/ℓ` with `ρ = (1+3π)α`:
  **`C2Comp_depth`** : `Σ_{c ℓⁿ-aligned} ‖suOf (C2CompL ℓ (bgTower V) n a c)‖ ≤ K2free ℓ ρ · ℓ⁻ⁿ · nrm₁(a)²`.
Route = DL74 `hK2_M0` with `k := n` and the M0 regime replaced by its three used inputs: RKF `regTower_M0_kuniform`
(`RegTower` to depth `n`), BC8 `towerClass_of_blocking` (class `ε_j = ℓʲe + 3π(ℓ²)ʲq₀`), DL73 `C2Comp_l1`, and the r8 bridge
`C2CompL_eq_C2CompX`.
* **`C2Comp_depth_any`** : the same on any lattice `L` with `scaleUp ℓ n Lu' = L` (transport by `subst`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1DStrat.DQ

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.IngredientFamilyR2 (C2CompL C2CompX C2CompL_eq_C2CompX bgTower Cfg XS RegTower)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (nrm nrm_nonneg rr thetaOf thetaOf_nonneg TowerClass)
open AdalyFormal.AsmM0 (rhoM0)
open AdalyFormal.RegBgKU (KUSmall)
open AdalyFormal.DLayer (C2Comp_l1 K2s K2free thetaK2 rhoOf_mono)
open AdalyFormal.CurvBlock (dv)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_mono e2Majorant_nonneg)

/-- the value of `rhoM0` at link scale `α/ℓⁿ` and plaquette scale `α/ℓ²ⁿ` -/
theorem rhoM0_alpha (ell n : ℕ) (hell : 0 < ell) (α : ℝ) :
    rhoM0 ell n (α / (ell : ℝ) ^ n) (α / ((ell : ℝ) ^ n) ^ 2) = (1 + 3 * Real.pi) * α := by
  unfold rhoM0
  have : (0 : ℝ) < (ell : ℝ) ^ n := by positivity
  field_simp

/-- **the composite second jet in `ℓ¹` at depth `n`** -/
theorem C2Comp_depth (ell n : ℕ) (Lu' : PeriodicLatticeExtent) (hell2 : 2 ≤ ell) (V : Cfg (scaleUp ell n Lu'))
    (α : ℝ) (hα : 0 ≤ α)
    (hlinks : ∀ b, dv (V b) ≤ α / (ell : ℝ) ^ n)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell n Lu'), dv (periodicPlaquetteHolonomy V p) ≤ α / ((ell : ℝ) ^ n) ^ 2)
    (hN : ∀ ρ, 2 * ell ^ n < scaleUp ell n Lu' ρ + 1)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * α ≤ 1)
    (H : KUSmall ell ((1 + 3 * Real.pi) * α))
    (h1000 : (1 + 3 * Real.pi) * α ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hK2c : 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ((1 + 3 * Real.pi) * α)) < 1 - 1 / (ell : ℝ))
    (a : XS (scaleUp ell n Lu')) :
    ∑ c : CoarseBond (scaleUp ell n Lu') (ell ^ n),
        ‖suOf (C2CompL ell (bgTower (GF ell n Lu') V) n a (c.1.1, c.2))‖
      ≤ K2free ell ((1 + 3 * Real.pi) * α) * (1 / (ell : ℝ)) ^ n * nrm 1 a ^ 2 := by
  have hell : 0 < ell := by omega
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
  have hpi := Real.pi_pos
  set nn : ℝ := (ell : ℝ) ^ n with hnn
  have hnpos : 0 < nn := by positivity
  set e : ℝ := α / nn with he
  set q0 : ℝ := α / nn ^ 2 with hq
  have he0 : 0 ≤ e := by positivity
  have hq0 : 0 ≤ q0 := by positivity
  set ρ : ℝ := (1 + 3 * Real.pi) * α with hρ
  have hρdef : rhoM0 ell n e q0 = ρ := rhoM0_alpha ell n hell α
  have hρ0 : 0 ≤ ρ := by positivity
  -- regularity and tower class at depth n
  have hreg : RegTower ell (bgTower (GF ell n Lu') V) n :=
    AdalyFormal.RegBgKU.regTower_M0_kuniform ell n Lu' hell2 V e q0 he0 hq0 hlinks hplaq (by rw [hρdef]; exact H)
  have hcbq : 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ n * q0) ≤ 1 := by
    have e1 : ((ell : ℝ) ^ 2) ^ n * q0 = α := by
      rw [hq, hnn, ← pow_mul, mul_comm 2 n, pow_mul]; field_simp
    rw [e1]; exact hcb
  set ε : ℕ → ℝ := fun j => (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0) with hεdef
  have hcl : TowerClass ell n Lu' V ε :=
    AdalyFormal.BondComposite.towerClass_of_blocking ell n Lu' hell2 V q0 e hq0
      (AdalyFormal.CurvBlock.pw_one_of_plaq V q0 hq0 hplaq) hlinks hN hcbq
  have hε0 : ∀ j, j < n → 0 ≤ ε j := fun j _ => by simp only [hεdef]; positivity
  set η' : ℝ := e + 3 * Real.pi * (nn * q0) with hη'
  have hη'0 : 0 ≤ η' := by positivity
  have hρη : ρ = nn * η' := by rw [← hρdef]; rfl
  have hεη : ∀ j, j ≤ n → ε j ≤ (ell : ℝ) ^ j * η' := fun j hj =>
    AdalyFormal.BondComposite.eps_class_le ell n (by omega) e q0 hq0 j hj
  have hερ : ∀ j, j ≤ n → ε j ≤ ρ := by
    intro j hj
    refine (hεη j hj).trans ?_
    rw [hρη]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hj) hη'0
  have hεs : ∀ j, j < n → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
    intro j hj
    have h1 : (ell : ℝ) ^ j * ell ≤ nn := by
      rw [hnn, ← pow_succ]; exact pow_le_pow_right₀ (by linarith) hj
    have h2 : (ell : ℝ) ^ j * η' ≤ ρ / ell := by
      rw [le_div_iff₀ hellR, hρη]
      nlinarith [mul_le_mul_of_nonneg_right h1 hη'0]
    have h3 : ρ / ell ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
      calc ρ / ell ≤ (1 / (1000 * (ell : ℝ) ^ 3)) / ell := div_le_div_of_nonneg_right h1000 hellR.le
        _ = 1 / (1000 * (ell : ℝ) ^ 4) := by field_simp
    exact (hεη j hj.le).trans (h2.trans h3)
  have hsm : ∀ j, j < n → rhoOf ell (ε j) < Real.pi / 2 := fun j hj =>
    AdalyFormal.BondComposite.hsm_of_le ell hell (ε j) (hε0 j hj) (hεs j hj)
  have hloop : ∀ j, j < n → 8 * (ell : ℝ) * ε j ≤ 1 / 16 := by
    intro j hj
    have h1 := hεs j hj
    have hl3 : (8 : ℝ) * ell ≤ 8 * (ell : ℝ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hl2 3]
    have h5 : 8 * (ell : ℝ) * ε j ≤ 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) := by
      have := mul_le_mul hl3 h1 (hε0 j hj) (by positivity)
      linarith
    have h6 : 8 * (ell : ℝ) ^ 4 * (1 / (1000 * (ell : ℝ) ^ 4)) = 8 / 1000 := by field_simp
    linarith
  set θ := thetaK2 ell ρ with hθ
  have hκ0 : 0 ≤ e2Majorant (rhoOf ell ρ) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  have hθ0 : 0 ≤ θ := by rw [hθ]; unfold thetaK2; positivity
  have hθ1 : θ < 1 := by rw [hθ]; unfold thetaK2; linarith
  have hA : ∀ j, j < n → 1 / (ell : ℝ) ^ 2 + 1536 * ell * e2Majorant (rhoOf ell (ε j)) ≤ θ / ell := by
    intro j hj
    have hmono : e2Majorant (rhoOf ell (ε j)) ≤ e2Majorant (rhoOf ell ρ) :=
      e2Majorant_mono (by unfold rhoOf; have := hε0 j hj; positivity) (rhoOf_mono ell (hερ j hj.le))
    have e1 : θ / ell = 1 / (ell : ℝ) ^ 2 + 1536 * ell * e2Majorant (rhoOf ell ρ) := by
      rw [hθ]; unfold thetaK2; field_simp
    rw [e1]
    have := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1536 * ell)
    linarith
  have hmain := C2Comp_l1 ell n Lu' hell V ε hreg hcl hε0 hsm hloop θ hθ0 hθ1 hA a
  rw [← C2CompL_eq_C2CompX ell (bgTower (GF ell n Lu') V) n hreg n le_rfl] at hmain
  have hS : ∑ i ∈ Finset.range n, thetaOf ell (ε i) ≤ 3600 * (ell : ℝ) * ρ := by
    have h := AdalyFormal.BondComposite.S_le ell n hell2 ε η' hη'0 hε0 (fun j hj => hεη j hj.le) hεs
    rw [hρη]; exact h
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hexp : Real.exp ((∑ i ∈ Finset.range n, thetaOf ell (ε i)) / rr ell) ^ 2
      ≤ Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have := div_le_div_of_nonneg_right hS hr.le
    push_cast
    have e2 : 2 * (3600 * (ell : ℝ) * ρ) / rr ell = 2 * ((3600 * (ell : ℝ) * ρ) / rr ell) := by ring
    rw [e2]; linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hK : 0 ≤ K2s ell := by unfold K2s; positivity
  have hX := nrm_nonneg 1 a
  refine hmain.trans ?_
  have hpow : (0 : ℝ) ≤ (1 / (ell : ℝ)) ^ n := by positivity
  have h2 : 0 ≤ K2s ell * ell / (1 - θ) * nrm 1 a ^ 2 * (1 / (ell : ℝ)) ^ n := by positivity
  have := mul_le_mul_of_nonneg_left hexp h2
  have e3 : K2s ell * (Real.exp ((∑ i ∈ Finset.range n, thetaOf ell (ε i)) / rr ell) * nrm 1 a) ^ 2 * ell / (1 - θ)
      * (1 / (ell : ℝ)) ^ n = K2s ell * ell / (1 - θ) * nrm 1 a ^ 2 * (1 / (ell : ℝ)) ^ n
        * Real.exp ((∑ i ∈ Finset.range n, thetaOf ell (ε i)) / rr ell) ^ 2 := by ring
  have e4 : K2free ell ρ * (1 / (ell : ℝ)) ^ n * nrm 1 a ^ 2
      = K2s ell * ell / (1 - θ) * nrm 1 a ^ 2 * (1 / (ell : ℝ)) ^ n * Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) := by
    unfold K2free; rw [← hθ]; field_simp
  rw [e3, e4]; exact this

/-- the same on any lattice identified with `scaleUp ℓ n Lu'` -/
theorem C2Comp_depth_any (ell n : ℕ) (Lu' L : PeriodicLatticeExtent) (hL : scaleUp ell n Lu' = L) (hell2 : 2 ≤ ell)
    (V : Cfg L) (α : ℝ) (hα : 0 ≤ α)
    (hlinks : ∀ b, dv (V b) ≤ α / (ell : ℝ) ^ n)
    (hplaq : ∀ p : PeriodicLatticePlaquette L, dv (periodicPlaquetteHolonomy V p) ≤ α / ((ell : ℝ) ^ n) ^ 2)
    (hN : ∀ ρ, 2 * ell ^ n < L ρ + 1)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * α ≤ 1)
    (H : KUSmall ell ((1 + 3 * Real.pi) * α))
    (h1000 : (1 + 3 * Real.pi) * α ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hK2c : 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ((1 + 3 * Real.pi) * α)) < 1 - 1 / (ell : ℝ))
    (a : XS L) :
    ∑ c : CoarseBond L (ell ^ n),
        ‖suOf (C2CompL ell (AdalyFormal.Balaban.UbarTowerCov.UbarTower AdalyFormal.Balaban.SuTwoLogExp.su2LogExp ell V)
          n a (c.1.1, c.2))‖
      ≤ K2free ell ((1 + 3 * Real.pi) * α) * (1 / (ell : ℝ)) ^ n * nrm 1 a ^ 2 := by
  subst hL
  exact C2Comp_depth ell n Lu' hell2 V α hα hlinks hplaq hN hcb H h1000 hK2c a

#print axioms rhoM0_alpha
#print axioms C2Comp_depth
#print axioms C2Comp_depth_any

end AdalyFormal.M1DStrat.DQ
