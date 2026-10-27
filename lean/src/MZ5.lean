import MZ4

/-!
# MZ5 -- assembly: `DLayerStrat` on the printed class, modulo the operator layer `OpLayer` (m2_dlayer, 2026-10-15)

`OpLayer` collects, at ONE configuration, the operator-level premises of the M1 D-layer in the shapes DS1 consumes, with the
column premises in their weighted-ℓ² (Combes–Thomas) form — the form the M1 chain proves on its regime from W4 + W6 + the CT
relative bounds (DY4b `H1_col`/`H_cjp_w`, DH1 `H_col`):
* `hHL2`  : `Σ_b (ℓ^{-strat b.1} e^{φ_c(b.1)} ‖(H δ_p v)(b)‖)² ≤ KH² ℓ^{strat c} ‖v‖²` for SOME centre `c` (`φ_c = phiC θ c`);
* `hH1L2` : the same for `H₁in δ_e v`;
* `hC2`, `hW`, `hKD` : DS1 `DParts` fields verbatim.
No clause-3 / M1Regular / global gauge appears in `OpLayer`.

* **`dlayerStrat_class`** : printed class (`ClassCoupled ℓ M 12`, `Admissible`, `4β ≤ 1`) + `OpLayer` ⇒ `DLayerStrat` with
  `ε2s ≥ 2(√Ageo KH · SJ) K2 CW`, `εJ ≥ (√Ageo KH1 · SJ) KD`, `SJ = 400 ℓ³ · 12 M α₀`.
* **`dlayerObligationClass_holds`** : for fixed `θ, KH, KH1, K2, CW, KD`, every pair of tolerances has a k-free `a₁`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1 (strat bstrat DLayerStrat wnormSq)
open AdalyFormal.M1DStrat (omJ phiC DParts dlayerStrat_of_parts)

/-- **the operator layer at one configuration** (named premises; no regularity hypothesis on `U` inside). -/
structure OpLayer (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (θ KH KH1 K2 CW KD : ℝ) : Prop where
  hHL2 : ∀ (p : BIdx (gparams ell k Lu hell S U a Lam).G) (v : SuTwo), ∃ c : PeriodicLatticeSite (scaleUp ell k Lu),
    ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (phiC S ell M R k θ c b.1)
      * ‖(iE (gparams ell k Lu hell S U a Lam).G ((gparams ell k Lu hell S U a Lam).data.H
          (WithLp.toLp 2 (Pi.single p v) : FSp (gparams ell k Lu hell S U a Lam).G))) b‖) ^ 2
      ≤ KH ^ 2 * (ell : ℝ) ^ strat S k c * ‖v‖ ^ 2
  hH1L2 : ∀ (e : Bond Lu) (v : SuTwo), ∃ c : PeriodicLatticeSite (scaleUp ell k Lu),
    ∑ b : Bond (scaleUp ell k Lu), ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (phiC S ell M R k θ c b.1)
      * ‖((gparams ell k Lu hell S U a Lam).H1in (WithLp.toLp 2 (Pi.single e v) : BondFnL2 Lu)) b‖) ^ 2
      ≤ KH1 ^ 2 * (ell : ℝ) ^ strat S k c * ‖v‖ ^ 2
  hC2 : ∀ z : BondFnL2 (scaleUp ell k Lu),
    ∑ p, ‖C2fullOf (gparams ell k Lu hell S U a Lam).G (gparams ell k Lu hell S U a Lam).U z p‖
      ≤ K2 * wnormSq (gparams ell k Lu hell S U a Lam).S (gparams ell k Lu hell S U a Lam).ell
        (gparams ell k Lu hell S U a Lam).k z
  hW : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
    wnormSq (gparams ell k Lu hell S U a Lam).S (gparams ell k Lu hell S U a Lam).ell (gparams ell k Lu hell S U a Lam).k
      (Wop (gparams ell k Lu hell S U a Lam).G (gparams ell k Lu hell S U a Lam).U (gparams ell k Lu hell S U a Lam).a
        (iE (gparams ell k Lu hell S U a Lam).G A))
      ≤ CW * wnormSq (gparams ell k Lu hell S U a Lam).S (gparams ell k Lu hell S U a Lam).ell
        (gparams ell k Lu hell S U a Lam).k (A : BondFnL2 (gparams ell k Lu hell S U a Lam).Lf)
  hKD : ∀ B : BondFnL2 Lu, ∑ e, ‖((gparams ell k Lu hell S U a Lam).D2in B) e‖ ≤ KD * ‖B‖ ^ 2

/-- the class source constant dominates the uncovered constant -/
theorem su_le_sj (ell : ℕ) (hell : 1 ≤ ell) (β : ℝ) (hβ0 : 0 ≤ β) (hsm : 4 * β ≤ 1) :
    4 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3) ≤ 400 * (ell : ℝ) ^ 3 * β := by
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl3 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ hellr
  have hb4 : β ≤ 1 / 4 := by linarith
  have a2 : β ^ 2 ≤ β * (1 / 4) := by nlinarith
  have a3 : β ^ 3 ≤ β * (1 / 16) := by nlinarith [pow_le_pow_left₀ hβ0 hb4 2]
  nlinarith

open Classical in
/-- **lane B's stratified D-layer premises at a printed-class configuration, modulo `OpLayer`** -/
theorem dlayerStrat_class {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hell2 : 2 ≤ ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)} (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M) (hRM : 4 ≤ R * M)
    (hU : ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    {θ : ℝ} (hθ : 0 < θ) (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)
    {KH KH1 K2 CW KD : ℝ} (hKH : 0 ≤ KH) (hKH1 : 0 ≤ KH1) (hK2 : 0 ≤ K2)
    (hop : OpLayer ell M R k Lu hell S U a Lam θ KH KH1 K2 CW KD)
    (ε2s εJ : ℝ)
    (h2 : 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * CW ≤ ε2s)
    (hJ : ((Real.sqrt (Ageo ell θ) * KH1) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * KD ≤ εJ) :
    DLayerStrat ell k Lu hell S U a Lam ε2s εJ := by
  set SJ : ℝ := 400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀) with hSJ
  have hell1 : 1 ≤ ell := hell
  have hβ0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hSJ0 : 0 ≤ SJ := by positivity
  have hcov : CoversOm0p ell M 12 k S := hU.1
  have hRM3 : 3 ≤ R * M := by omega
  refine dlayerStrat_of_parts ell k Lu hell S U a Lam ε2s εJ (omS ell M k S) SJ
    (Real.sqrt (Ageo ell θ) * KH) K2 CW (Real.sqrt (Ageo ell θ) * KH1) KD ?_ h2 hJ
  refine ⟨hSJ0, by positivity, hK2, by positivity, ?_, ?_, hop.hC2, hop.hW, ?_, hop.hKD⟩
  · -- the source, split
    intro b
    have h := Jf_split hell hS hRM hU hα hsm a Lam b
    have hsu := su_le_sj ell hell1 _ hβ0 hsm
    have hJ0 : 0 ≤ omJ S ell k b := by unfold omJ; positivity
    refine h.trans ?_
    unfold omS
    split_ifs with hu
    · have hU0 : 0 ≤ omU S ell k b := by unfold omU; positivity
      have := mul_le_mul_of_nonneg_right hsu hU0
      nlinarith
    · linarith
  · intro p v
    obtain ⟨c, hc⟩ := hop.hHL2 p v
    exact col_class hS hR hM hell2 hRM3 hcov hθ hq c _ (fun b => norm_nonneg _) KH ‖v‖ hKH (norm_nonneg _) hc
  · intro e v
    obtain ⟨c, hc⟩ := hop.hH1L2 e v
    exact col_class hS hR hM hell2 hRM3 hcov hθ hq c _ (fun b => norm_nonneg _) KH1 ‖v‖ hKH1 (norm_nonneg _) hc

/-- **the D-layer obligation on the printed class**, with the operator layer as a per-configuration premise with FIXED
constants (shape parallel to m1_dstrat DX6 `DLayerObligationW4`, with `M1Regular` replaced by the printed class). -/
def DLayerObligationClass (ell M R : ℕ) (hell : 0 < ell) (a θ KH KH1 K2 CW KD : ℝ) : Prop :=
  ∀ ε2s : ℝ, 0 < ε2s → ∀ εJ : ℝ, 0 < εJ → ∃ a₁ : ℝ, 0 < a₁ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₁ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M 12 k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    OpLayer ell M R k Lu hell S U a Lam θ KH KH1 K2 CW KD →
      DLayerStrat ell k Lu hell S U a Lam ε2s εJ

theorem dlayerObligationClass_holds {ell M R : ℕ} (hell : 0 < ell) (hell2 : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hRM : 4 ≤ R * M) (a : ℝ) {θ : ℝ} (hθ : 0 < θ) (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)
    {KH KH1 K2 CW KD : ℝ} (hKH : 0 ≤ KH) (hKH1 : 0 ≤ KH1) (hK2 : 0 ≤ K2) (hCW : 0 ≤ CW) (hKD : 0 ≤ KD) :
    DLayerObligationClass ell M R hell a θ KH KH1 K2 CW KD := by
  intro ε2s hε2s εJ hεJ
  set A := Real.sqrt (Ageo ell θ) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set C1 : ℝ := 2 * (A * KH) * (400 * (ell : ℝ) ^ 3) * K2 * CW with hC1
  set C2 : ℝ := (A * KH1) * (400 * (ell : ℝ) ^ 3) * KD with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨min (1 / 4) (min (ε2s / (C1 + 1)) (εJ / (C2 + 1))),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), ?_⟩
  intro k hk Lu α₀ hα ht hT S hS hcov Lam hL U hU hop
  set β : ℝ := (12 : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hb4 : β ≤ 1 / 4 := ht.trans (min_le_left _ _)
  have hb1 : β ≤ ε2s / (C1 + 1) := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb2 : β ≤ εJ / (C2 + 1) := ht.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : C1 * β ≤ ε2s := by
    have h := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ C1 + 1 by linarith)
    rw [mul_div_cancel₀ _ (by positivity : (C1 + 1 : ℝ) ≠ 0)] at h
    nlinarith
  have hc2 : C2 * β ≤ εJ := by
    have h := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ C2 + 1 by linarith)
    rw [mul_div_cancel₀ _ (by positivity : (C2 + 1 : ℝ) ≠ 0)] at h
    nlinarith
  refine dlayerStrat_class hell hell2 a Lam hS hR hM hRM hU hα.le (by linarith) hθ hq hKH hKH1 hK2 hop ε2s εJ ?_ ?_
  · calc 2 * ((A * KH) * (400 * (ell : ℝ) ^ 3 * β)) * K2 * CW = C1 * β := by rw [hC1]; ring
      _ ≤ ε2s := hc1
  · calc ((A * KH1) * (400 * (ell : ℝ) ^ 3 * β)) * KD = C2 * β := by rw [hC2]; ring
      _ ≤ εJ := hc2

#print axioms OpLayer
#print axioms su_le_sj
#print axioms dlayerStrat_class
#print axioms DLayerObligationClass
#print axioms dlayerObligationClass_holds

end AdalyFormal.M2DLayer
