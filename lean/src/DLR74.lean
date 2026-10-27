import DLR73
import DLR53

/-!
# DL74 -- **premise `hK2` of DL5 at M0**: `Σ_p ‖C2fullOf G U z p‖ ≤ K2free·n⁻²·‖z‖²`, `K2free` k- and volume-free

* `C2full_apply_level` : `C2fullOf G V z p = (ℓ^{p.1})⁻¹ • suOf (C2CompX ℓ (bgTower G V) p.1 (suCoord z) p.2.1)`
  (the frozen r7 object, via `C2rawB_eq`);
* `C2full_l1` : on the full tower, `Σ_p ‖C2fullOf‖ ≤ n⁻¹ Σ_{c ℓ^k-aligned} ‖suOf (C_k(suCoord z) c)‖` (BC6 `bidxCB`, injective);
* `eps_le_rho` : `epsCl ℓ e q0 j ≤ ρ` for `j ≤ k`;
* **`hK2_M0`** : under `M0RegimeR` + `KUSmall` and the k-free contraction condition
  `hK2c : 1536·ℓ²·e2Majorant(rhoOf ℓ ρ) < 1 − 1/ℓ`,
    `Σ_p ‖C2fullOf (PU ..).G U z p‖ ≤ K2free ℓ ρ / n² · ‖z‖²`,
    `K2free ℓ ρ = K2s ℓ · e^{2·3600ℓρ/rr ℓ} · ℓ / (1 − θ)`,  `θ = 1/ℓ + 1536·ℓ²·e2Majorant(rhoOf ℓ ρ)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2 (QlinCompX C2CompX RegTower XS toM2 bgTower Cfg C2fullOf C2rawB C2rawB_eq suCoord
  suCoordInv TowerGeom BIdx)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (nrm rr thetaOf TowerClass bidx_level bidxCB bidxCB_injective sum_le_of_injective
  nrm_one_suCoord)
open AdalyFormal.AsmM0 (rhoM0 M0RegimeR)
open AdalyFormal.RegBgKU (KUSmall regTower_M0_kuniform)
open AdalyFormal.M0Finish (PU)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_mono e2Majorant_nonneg)

-- r8 PORT: `C2rawB` is built on the LOCAL jet `C2CompL`; the r7 form holds on a regular tower (bridge `C2rawB_eq_r7`),
-- so the hypothesis `hreg` is added (every call site has it).
theorem C2full_apply_level {L : PeriodicLatticeExtent} (G : TowerGeom L) (V : Cfg L)
    (hreg : RegTower G.ell (bgTower G V) G.k) (z : BondFnL2 L) (p : BIdx G) :
    C2fullOf G V z p = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (C2CompX G.ell (bgTower G V) p.1 (suCoord z) p.2.1) := by
  have hj : (p.1 : ℕ) ≤ G.k := Nat.lt_succ_iff.mp p.1.isLt
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G V p.1 z)) p.2.1 = _
  rw [AdalyFormal.IngredientFamilyR2.C2rawB_eq_r7 G V G.k hreg p.1 hj]; rfl

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

theorem C2full_l1 (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (z : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p : BIdx (GF ell k Lu), ‖C2fullOf (GF ell k Lu) U z p‖
      ≤ ((ell : ℝ) ^ k)⁻¹ * ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ k),
          ‖suOf (C2CompX ell (bgTower (GF ell k Lu) U) k (suCoord z) (c.1.1, c.2))‖ := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  set g : CoarseBond (scaleUp ell k Lu) (ell ^ k) → ℝ :=
    fun c => ‖suOf (C2CompX ell (bgTower (GF ell k Lu) U) k (suCoord z) (c.1.1, c.2))‖ with hg
  have hgn : ∀ c, 0 ≤ g c := fun c => norm_nonneg _
  have key : ∀ n : ℕ, n = k → ∀ b : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu),
      ‖((ell : ℝ) ^ n)⁻¹ • suOf (C2CompX ell (bgTower (GF ell k Lu) U) n (suCoord z) b)‖
        = ((ell : ℝ) ^ k)⁻¹ * ‖suOf (C2CompX ell (bgTower (GF ell k Lu) U) k (suCoord z) (b.1, b.2))‖ := by
    intro n hn b
    subst hn
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hper : ∀ p : BIdx (GF ell k Lu), ‖C2fullOf (GF ell k Lu) U z p‖ = ((ell : ℝ) ^ k)⁻¹ * g (bidxCB ell k Lu hell p) := by
    intro p
    rw [C2full_apply_level _ _ hreg]
    exact key (p.1 : ℕ) (bidx_level ell k Lu p) p.2.1
  rw [Finset.sum_congr rfl fun p _ => hper p, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_le_of_injective _ (bidxCB_injective ell k Lu hell) g hgn) (by positivity)

theorem eps_le_rho (hell : 1 ≤ ell) (e q0 : ℝ) (he0 : 0 ≤ e) (hq0 : 0 ≤ q0) (j : ℕ) (hj : j ≤ k) :
    epsCl ell e q0 j ≤ rhoM0 ell k e q0 := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h1 : (ell : ℝ) ^ j ≤ (ell : ℝ) ^ k := pow_le_pow_right₀ hl1 hj
  have h2 : ((ell : ℝ) ^ 2) ^ j ≤ ((ell : ℝ) ^ 2) ^ k := pow_le_pow_right₀ (by nlinarith) hj
  have hρ : rhoM0 ell k e q0 = (ell : ℝ) ^ k * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ k * q0) := by
    unfold rhoM0
    have : ((ell : ℝ) ^ 2) ^ k = ((ell : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [this]; ring
  unfold epsCl
  rw [hρ]
  have hpi := Real.pi_pos
  have := mul_le_mul_of_nonneg_right h1 he0
  have := mul_le_mul_of_nonneg_right h2 hq0
  nlinarith

end

/-- the k-free constants -/
noncomputable def thetaK2 (ell : ℕ) (ρ : ℝ) : ℝ := 1 / (ell : ℝ) + 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ρ)

noncomputable def K2free (ell : ℕ) (ρ : ℝ) : ℝ :=
  K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) * ell / (1 - thetaK2 ell ρ)

theorem rhoOf_mono (ell : ℕ) {a b : ℝ} (hab : a ≤ b) : rhoOf ell a ≤ rhoOf ell b := by
  unfold rhoOf
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab (by positivity)) (by positivity)

/-- **premise hK2 of DL5 at M0** -/
theorem hK2_M0 (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (Lam : Set (PeriodicLatticeSite Lu))
    (hK2c : 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell (rhoM0 ell k e q0)) < 1 - 1 / (ell : ℝ))
    (z : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, ‖C2fullOf (PU ell k Lu hell U a Lam).G U z p‖
      ≤ K2free ell (rhoM0 ell k e q0) / ((ell : ℝ) ^ k) ^ 2 * ‖z‖ ^ 2 := by
  have hell2 : 2 ≤ ell := R.hell
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
  set ρ := rhoM0 ell k e q0 with hρdef
  have hρ0 : 0 ≤ ρ := m0_rho_nonneg ell k Lu U a t e q0 R
  set ε := epsCl ell e q0 with hε
  have hreg : RegTower ell (bgTower (GF ell k Lu) U) k :=
    regTower_M0_kuniform ell k Lu hell2 U e q0 R.he0 R.hq0 R.hlinks R.hplaq H
  have hcl : TowerClass ell k Lu U ε := m0_cl ell k Lu U a t e q0 R
  have hε0 := m0_hε0 ell k Lu U a t e q0 R
  have hsm := m0_hsm ell k Lu U a t e q0 R
  have hεs := m0_hεs ell k Lu U a t e q0 R
  have hloop : ∀ j, j < k → 8 * (ell : ℝ) * ε j ≤ 1 / 16 := by
    intro j hj
    have h1 := hεs j hj
    have h4 : (16 : ℝ) ≤ (ell : ℝ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hl2 4]
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
  have hA : ∀ j, j < k → 1 / (ell : ℝ) ^ 2 + 1536 * ell * e2Majorant (rhoOf ell (ε j)) ≤ θ / ell := by
    intro j hj
    have hεj : ε j ≤ ρ := eps_le_rho ell k (by omega) e q0 R.he0 R.hq0 j hj.le
    have hmono : e2Majorant (rhoOf ell (ε j)) ≤ e2Majorant (rhoOf ell ρ) :=
      e2Majorant_mono (by unfold rhoOf; have := hε0 j hj; positivity) (rhoOf_mono ell hεj)
    have e1 : θ / ell = 1 / (ell : ℝ) ^ 2 + 1536 * ell * e2Majorant (rhoOf ell ρ) := by
      rw [hθ]; unfold thetaK2; field_simp
    rw [e1]
    have := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1536 * ell)
    linarith
  have hmain := C2Comp_l1 ell k Lu hell U ε hreg hcl hε0 hsm hloop θ hθ0 hθ1 hA (suCoord z)
  have hlevel := C2full_l1 ell k Lu hell U hreg z
  rw [nrm_one_suCoord] at hmain
  have hS := m0_S ell k Lu U a t e q0 R
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hexp : Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) ^ 2
      ≤ Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have := div_le_div_of_nonneg_right hS hr.le
    push_cast
    have e2 : 2 * (3600 * (ell : ℝ) * ρ) / rr ell = 2 * ((3600 * (ell : ℝ) * ρ) / rr ell) := by ring
    rw [e2]; linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hpow : (1 / (ell : ℝ)) ^ k = ((ell : ℝ) ^ k)⁻¹ := by rw [one_div, inv_pow]
  -- combine
  have hz := norm_nonneg z
  have hK : 0 ≤ K2s ell := by unfold K2s; positivity
  have hB : K2s ell * (Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) * ‖z‖) ^ 2 * ell / (1 - θ)
        * (1 / (ell : ℝ)) ^ k
      ≤ K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) * ell / (1 - θ) * ‖z‖ ^ 2 * ((ell : ℝ) ^ k)⁻¹ := by
    rw [mul_pow, hpow]
    have h2 : 0 ≤ K2s ell * ell / (1 - θ) * ‖z‖ ^ 2 * ((ell : ℝ) ^ k)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hexp h2
    have e3 : K2s ell * (Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) ^ 2 * ‖z‖ ^ 2) * ell / (1 - θ)
        * ((ell : ℝ) ^ k)⁻¹ = K2s ell * ell / (1 - θ) * ‖z‖ ^ 2 * ((ell : ℝ) ^ k)⁻¹
          * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell) ^ 2 := by ring
    have e4 : K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) * ell / (1 - θ) * ‖z‖ ^ 2 * ((ell : ℝ) ^ k)⁻¹
        = K2s ell * ell / (1 - θ) * ‖z‖ ^ 2 * ((ell : ℝ) ^ k)⁻¹ * Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) := by ring
    rw [e3, e4]; exact this
  have hfin := (hlevel.trans (mul_le_mul_of_nonneg_left (hmain.trans hB) (by positivity)))
  refine hfin.trans (le_of_eq ?_)
  unfold K2free
  rw [← hθ]
  field_simp

#print axioms C2full_apply_level
#print axioms C2full_l1
#print axioms eps_le_rho
#print axioms hK2_M0

end AdalyFormal.DLayer
