import DN0
import DP1
import DU1
import DR1
import GW5

/-!
# DX1 -- the first D-layer clause (`hD2`, stratified) at a configuration of the M1 regime (M1 D-layer lane, 2026-10-14)

From the M1 data `U^g = exp(iηA)`, `M1Bounds … 12 … α₀ η A` (`η = ℓ^{-k}`), every structural input of DP1's
`dlayer_clause1` is produced at `V = U^g` with NO named input:
* `hlink_all` : `frob(V_b − 1) ≤ ρ₁ / ℓ^{bstrat b}` on EVERY bond (cube chart on the class `{e : bstrat b ≤ bstrat e}`);
* the `HatPack`, the two-sided inverse `Gi` of `Γ = X*X`, the row bound `γ` (lane E MI28 / MS6 / MI27, lane C GW2);
* `RegData` (towerloc `regData_M1`), `HolRegime` (GW2), `Q*` injective (towerloc `qs_injective_M1`);
* the energy right inverse `hext` (`bond_rightinv_M1` + DU1 `hext_of_rightinv`), `bN = bNext`;
* `M1Regular` at `V` (trivial gauge).
Remaining hypotheses: W4 at `V` (constant `cw`), and NUMERIC conditions on explicit real functions of
`(ℓ, a, θ, W, ρ₁ = rho1 12 M α₀, ρT = rhoT ℓ 12 M α₀, S* = SstarM ℓ 12 M α₀, cw, ε1, CH)` (DN0 twins).
* **`clause1_Ug`** : `|⟪A, Δ⁽²⁾ A⟫| ≤ eps2N … · wnormSq A` at `V`;
* **`clause1_U`** : the same bound at `U` (gauge invariance, GW1), from W4 at `U`.
No sorry / native_decide / axiom.
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
open AdalyFormal.TowerLoc (RegData Estar rho1 rho1_nonneg SstarM delStar regData_M1 qs_injective_M1)
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.M1 (M1Regular M1Bounds strat bstrat wnormSq)
open AdalyFormal.M1DStrat.DQ
open AdalyFormal.M1GaugeW4 (rhoT rhoT_nonneg rhoT_smalls epsXnum site_hU_M1 site_hT_M1 holRegime_M1 hbig_of
  ginv_gauge wnormSq_adEL delta2_gauge)
open AdalyFormal.CurvBlock (CubeChart cube_link dv)
open AdalyFormal.W6 (CwE CgE)

/-! ## 1. the link bound on every bond -/

/-- **`hlink` on all bonds** at `U^g`: `frob(U^g_b − 1) ≤ ρ₁ / ℓ^{bstrat b}`. -/
theorem hlink_all {L : PeriodicLatticeExtent} {ell M f k : ℕ} (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) (b : Bond L) :
    frobNorm (((periodicGaugeTransform g U b : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
      ≤ rho1 f M α₀ / (ell : ℝ) ^ bstrat S k b := by
  let K : CubeChart U (fun e => bstrat S k b ≤ bstrat S k e) η
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ bstrat S k b * η)⁻¹ ^ 1))
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ bstrat S k b * η)⁻¹ ^ 2)) :=
    { g := g
      A := A
      hA := fun e he => ⟨hB.1 e, hU e, hB.2.1 e _ he⟩
      hD := fun μ ν x h1 h2 => hB.2.2.1 μ ν x _ h1 h2 }
  have hK : dv (periodicGaugeTransform g U b)
      ≤ η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ bstrat S k b * η)⁻¹ ^ 1)) := cube_link hη K b le_rfl
  have hp : (0 : ℝ) < (ell : ℝ) ^ bstrat S k b := pow_pos (by exact_mod_cast hell) _
  have e1 : η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ bstrat S k b * η)⁻¹ ^ 1))
      = (f : ℝ) * M * α₀ / (ell : ℝ) ^ bstrat S k b := by
    field_simp
  rw [e1] at hK
  refine hK.trans ?_
  unfold rho1
  apply div_le_div_of_nonneg_right _ hp.le
  have := Real.pi_pos
  nlinarith

/-! ## 2. gauge transfers (both directions) -/

section gauge
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

/-- W4 at `U` gives W4 at `U^γ` -/
theorem coercive_to_gauge (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) (c : ℝ)
    (h : ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      c * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫)
    (A' : ↥(bondSupp (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).G)) :
    c * wnormSq S ell k (A' : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A', (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Ginv A'⟫ := by
  set A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G) :=
    (AdalyFormal.GaugeCov.adEL γ (gparams ell k Lu hell S U a Lam).G).symm A' with hA
  have hA' : A' = AdalyFormal.GaugeCov.adEL γ (gparams ell k Lu hell S U a Lam).G A := by
    rw [hA, LinearIsometryEquiv.apply_symm_apply]
  rw [hA', ginv_gauge hell S a Lam U γ A, wnormSq_adEL hell S a Lam U γ A]
  exact h A

/-- the stratified `Δ⁽²⁾` form bound at `U^γ` gives it at `U` -/
theorem dlayer_form_ungauge (U : LinkCfg (scaleUp ell k Lu)) (γ : GaugeFn (scaleUp ell k Lu)) (ε : ℝ)
    (h : ∀ A' : ↥(bondSupp (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).G),
      |⟪A', (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data.Delta2
          (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam).data_laws A'⟫|
        ≤ ε * wnormSq S ell k (A' : BondFnL2 (scaleUp ell k Lu)))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    |⟪A, (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws A⟫|
      ≤ ε * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu)) := by
  have h1 := h (AdalyFormal.GaugeCov.adEL γ (gparams ell k Lu hell S U a Lam).G A)
  rw [delta2_gauge hell S a Lam U γ A, wnormSq_adEL hell S a Lam U γ A] at h1
  exact h1

end gauge

/-! ## 3. numeric functions -/

/-- `γ` of lane E's `gamma_sharp` -/
noncomputable def gamN (ell W : ℕ) (a ρ : ℝ) : ℝ :=
  (ell : ℝ) * (Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a))
    / ((1 - 12 * ρ) ^ 2 - Real.sqrt (max a 1) * ((1 + 12 * ρ) ^ 2 + (512 * ρ ^ 2 + 4704) / a) * epsXnum ell W a ρ)

/-- the CT pair `(Θ, Δ)` at the D2 weight -/
noncomputable def ThN (ell W : ℕ) (θ : ℝ) : ℝ := 3 * θ * (ell : ℝ) ^ 2 + 2 * (ell : ℝ) ^ 2 * Real.log ell / W
noncomputable def DeN (ell W : ℕ) (θ : ℝ) : ℝ := 6 * θ + 3 * (ell : ℝ) * Real.log ell / W

/-- `bN` of the energy right inverse -/
noncomputable def bNext (ell W : ℕ) (a cs ρ ε1 : ℝ) : ℝ :=
  (1 + etaS ell W cs ρ ε1) * (90 * (4 * CgE ell) + (96 * (ell : ℝ) ^ 2 + 24) * ρ ^ 2 * (4 * CwE ell)) / a
    + 2 * ((17 / Real.sqrt 2) * 12 * (ρ * (ell : ℝ) ^ 4)) * (4 * CwE ell) / a + (1 + etaS ell W cs ρ ε1)

/-- `CWc` of DC1 -/
noncomputable def CWcN (ell W : ℕ) (a cs γ : ℝ) : ℝ :=
  1 + (ell : ℝ) * ((Real.sqrt 24 + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)
          * Real.sqrt (48 / cs))
      + (Real.sqrt (12 / cs) + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
        * ((ell : ℝ) ^ 2 * ((4 / cs)
          * ((Real.sqrt (max a 1) + Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1))
            * (γ ^ 2 * ((Real.sqrt (12 / cs)
                + Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1) * (4 / cs))
              * (Real.sqrt (max a 1) + Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1))))))))

/-- the D2 output constant -/
noncomputable def eps2N (ell M W : ℕ) (a θ α₀ CH cs γ : ℝ) : ℝ :=
  2 * ((Real.sqrt (3 * (ell : ℝ) ^ 7 * a * Cgeo ell θ) * CH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)))
    * K2strat ell (12 * M * α₀) * ((ell : ℝ) ^ 2 * CWcN ell W a cs γ ^ 2)

/-! ## 4. the `CTBase` of the M1 regime -/

section m1
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {W : ℕ}
  (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hroom : 18 * ell ≤ R * M) (hM : 0 < M) (hR8 : 8 * ell ≤ R)
  (hLu5 : ∀ μ, 5 ≤ Lu μ + 1) (hW : 1 ≤ W) (hWR : W ≤ R * M * ell)
  (U : LinkCfg (scaleUp ell k Lu))
  (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
  (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
  (hU : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp ((((((ell : ℝ) ^ k)⁻¹ : ℝ) : ℂ) * Complex.I) • A e))
  (hB : M1Bounds S ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ A) (hα0 : 0 ≤ α₀)
  (ha1 : (12 : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M α₀ ≤ 1)
  (a : ℝ) (ha : 0 < a) (θ : ℝ) (hθ : 0 < θ)
  (hsm0 : 24 * ((Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2
          + 1 * (Real.sqrt a * (Real.exp (3 * (ell : ℝ) * Real.log ell / W) - 1)) ^ 2) ≤ csOf a (rhoT ell 12 M α₀))
  (hsmD0 : 4 * (Real.sqrt 3 * (Real.exp (2 * (ell : ℝ) ^ 2 * Real.log ell / W) - 1)) ^ 2 ≤ csOf a (rhoT ell 12 M α₀))
  (hsmθ : 24 * ((Real.sqrt 3 * (Real.exp (ThN ell W θ) - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp (DeN ell W θ) - 1)) ^ 2)
    ≤ csOf a (rhoT ell 12 M α₀))
  (hsmDθ : 4 * (Real.sqrt 3 * (Real.exp (ThN ell W θ) - 1)) ^ 2 ≤ csOf a (rhoT ell 12 M α₀))
  (hgs : Real.sqrt (max a 1) * ((1 + 12 * rhoT ell 12 M α₀) ^ 2 + (512 * rhoT ell 12 M α₀ ^ 2 + 4704) / a)
        * epsXnum ell W a (rhoT ell 12 M α₀) < (1 - 12 * rhoT ell 12 M α₀) ^ 2)

include hell2 hS hroom hR8 hLu5 hW hWR hU hB hα0 ha1 hsm4 ha hsm0 hsmD0 in
theorem hatPack_M1 :
    HatPack (ell := ell) (k := k) (S := S) (W := W) (periodicGaugeTransform g U) a (csOf a (rhoT ell 12 M α₀)) := by
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  obtain ⟨h216, -⟩ := rhoT_smalls ell 12 M α₀ hα0 (by omega) hsm4
  exact hatPack_of hS hell2 _ a ha _ (rhoT_nonneg ell 12 M α₀ hα0) h216
    (site_hU_M1 hell2 (hS := hS) U g A hU hB hη hα0)
    (site_hT_M1 hell2 hS (by nlinarith) (hbig_of ell k Lu hLu5) U g A hU hB hη hα0 ha1 hsm4) hsm0 hsmD0

include hell2 hS hroom hR8 hLu5 hW hWR hU hB hα0 ha1 hsm4 ha in
theorem exists_Gi_M1 :
    ∃ Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S),
      (∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) (periodicGaugeTransform g U) a)
        ∘L Xop (geomOf ell k S) (periodicGaugeTransform g U) a) (Gi u) = u) ∧
      (∀ u, Gi ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) (periodicGaugeTransform g U) a)
        ∘L Xop (geomOf ell k S) (periodicGaugeTransform g U) a) u) = u) := by
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  obtain ⟨h216, -⟩ := rhoT_smalls ell 12 M α₀ hα0 (by omega) hsm4
  exact exists_Gami_strat ell k hell2 (hdvd_of_admissible hS) (properTower_geomOf (by omega) hS) _ a ha _
    (rhoT_nonneg ell 12 M α₀ hα0) h216
    (site_hU_M1 hell2 (hS := hS) U g A hU hB hη hα0)
    (site_hT_M1 hell2 hS (by nlinarith) (hbig_of ell k Lu hLu5) U g A hU hB hη hα0 ha1 hsm4)

include hell2 hS hroom hR8 hLu5 hW hWR hU hB hα0 ha1 hsm4 ha hsm0 hsmD0 hgs in
theorem gamN_pos : 0 < gamN ell W a (rhoT ell 12 M α₀) := by
  unfold gamN
  have hρ := rhoT_nonneg ell 12 M α₀ hα0
  have hq : 0 < Real.sqrt (max a 1) := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hb : 0 < (1 + 12 * rhoT ell 12 M α₀) ^ 2 + (512 * rhoT ell 12 M α₀ ^ 2 + 4704) / a := by positivity
  have hl : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hd : 0 < (1 - 12 * rhoT ell 12 M α₀) ^ 2 - Real.sqrt (max a 1)
      * ((1 + 12 * rhoT ell 12 M α₀) ^ 2 + (512 * rhoT ell 12 M α₀ ^ 2 + 4704) / a)
      * epsXnum ell W a (rhoT ell 12 M α₀) := by linarith
  positivity

include hell2 hS hroom hM hR8 hLu5 hW hWR hU hB hα0 ha1 hsm4 ha hsm0 hsmD0 hgs in
theorem gam_M1 (u : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖
      ≤ gamN ell W a (rhoT ell 12 M α₀) * ‖Xop (geomOf ell k S) (periodicGaugeTransform g U) a u‖ := by
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by
    have : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  obtain ⟨-, h12⟩ := rhoT_smalls ell 12 M α₀ hα0 (by omega) hsm4
  exact gamma_sharp hS hW hell2 (by omega) (by omega) hWR _ a _
    (hatPack_M1 hell2 hS hroom hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha hsm0 hsmD0)
    _ (rhoT_nonneg ell 12 M α₀ hα0) h12
    (site_hU_M1 hell2 (hS := hS) U g A hU hB hη hα0)
    (site_hT_M1 hell2 hS (by nlinarith) (hbig_of ell k Lu hLu5) U g A hU hB hη hα0 ha1 hsm4) hgs u

include hell2 hS hroom hM hR8 hLu5 hW hWR hU hB hα0 ha1 hsm4 ha hsm0 hsmD0 hθ hsmθ hsmDθ hgs in
/-- **the CT base of the M1 regime** at `V = U^g` -/
noncomputable def ctM1 : CTBase ell M R k S W where
  hS := hS
  hW := hW
  hell := hell2
  hR := by omega
  hM := by omega
  hWR := hWR
  U := periodicGaugeTransform g U
  a := a
  cs := csOf a (rhoT ell 12 M α₀)
  hp := hatPack_M1 hell2 hS hroom hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha hsm0 hsmD0
  θ := θ
  hθ := hθ
  Θ := ThN ell W θ
  Δ := DeN ell W θ
  hΘ := le_rfl
  hΔ := by unfold DeN; linarith
  hsm := hsmθ
  hsmD := hsmDθ
  Gi := Classical.choose (exists_Gi_M1 hell2 hS hroom hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha)
  hG1 := (Classical.choose_spec (exists_Gi_M1 hell2 hS hroom hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha)).1
  hG2 := (Classical.choose_spec (exists_Gi_M1 hell2 hS hroom hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha)).2
  γ := gamN ell W a (rhoT ell 12 M α₀)
  hγ0 := gamN_pos hell2 hS hroom hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha hsm0 hsmD0 hgs
  hγ := gam_M1 hell2 hS hroom hM hR8 hLu5 hW hWR U g A hU hB hα0 ha1 hsm4 a ha hsm0 hsmD0 hgs

end m1

#print axioms hlink_all
#print axioms coercive_to_gauge
#print axioms dlayer_form_ungauge
#print axioms gamN
#print axioms ThN
#print axioms DeN
#print axioms bNext
#print axioms CWcN
#print axioms eps2N
#print axioms hatPack_M1
#print axioms exists_Gi_M1
#print axioms gamN_pos
#print axioms gam_M1
#print axioms ctM1

end AdalyFormal.M1DStrat
