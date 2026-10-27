import MXQ_Base
import CJ5

/-!
# MXQ_CJ -- `plaq_small_class`, `classRows_read`, `classRows_unit` of the class_jets_diff lane for the MIXED hybrid class (lane mixed_20261017)

Text copies (tools/gen_cj.py) with `ClassCoupled ell M c` replaced by `ClassCoupledHQ ell M Fm bf` (bound factor `bf`, `a = bf M α₀`); the covering cube of a plaquette is any cube whose factor lies in Fm.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MXQ.ClassJets
open MXQ.AllC (CF CubeFamOK)

open AdalyFormal.ClassJets
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist pcd Tower Admissible towerBj DescribedAt IsClassCube CubeBond HT bigSide scaleUp TorusOK
  LambdaOK LamPrime CRowIn)
open AdalyFormal.StatementLane2 (ClassCoupled PerCubeRegular2 CoversPlaqOm0c)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CurvBlock (dv pw ladS ladPlaqs pathBonds off Box GoodPl curv_tower_na_loc loopVar_eq_ladS ladS_le
  mem_ladPlaqs ladPlaqs_aligned dv_conj dv_inv dv_one dv_nonneg CubeChart cube_plaq HTm plaqIn)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open MXQ.AllC

variable {L : PeriodicLatticeExtent}

/-- **fine plaquettes inside `Ω_m` are small.** -/
theorem plaq_small_classΦ {ell M bf k R : ℕ} {Fm : CF} [CubeFamOK Fm] {S : Tower L} {α₀ η : ℝ} {U : PeriodicLinkConfiguration SU2 L}
    (hell : 1 ≤ ell) (hη : 0 < η) (hS : Admissible ell M R k S) (hU : ClassCoupledHQ ell M Fm bf k S α₀ η U)
    (ha0 : 0 ≤ (bf : ℝ) * M * α₀) (ha1 : (bf : ℝ) * M * α₀ ≤ 1)
    {m : ℕ} (z : PeriodicLatticeSite L) (hz : Ball z 2 ⊆ S.Om m) (ν μ : Fin 3) :
    dv (pw 1 U z ν μ) ≤ (4 * Real.pi + 4) * ((bf : ℝ) * M * α₀) / (((ell : ℝ) ^ 2) ^ (m - 1)) := by
  set a : ℝ := (bf : ℝ) * M * α₀ with ha
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpos : (0 : ℝ) < ((ell : ℝ) ^ 2) ^ (m - 1) := by positivity
  have hB0 : 0 ≤ (4 * Real.pi + 4) * a / (((ell : ℝ) ^ 2) ^ (m - 1)) := by
    have := Real.pi_pos; positivity
  -- the oriented case
  have main : ∀ ν μ : Fin 3, ν < μ → dv (pw 1 U z ν μ) ≤ (4 * Real.pi + 4) * a / (((ell : ℝ) ^ 2) ^ (m - 1)) := by
    intro ν μ hνμ
    have hmem : ∀ w, pdist z w ≤ 2 → w ∈ S.Om 0 := fun w hw => om_anti hS (Nat.zero_le m) (hz hw)
    have s1 := pdist_shift_le z ν
    have s2 := pdist_shift_le z μ
    have s3 := pdist_shift_le (periodicLatticeShift z ν) μ
    have s4 := pdist_shift_le (periodicLatticeShift z μ) ν
    have t3 := pdist_triangle z (periodicLatticeShift z ν) (periodicLatticeShift (periodicLatticeShift z ν) μ)
    have t4 := pdist_triangle z (periodicLatticeShift z μ) (periodicLatticeShift (periodicLatticeShift z μ) ν)
    have hz0 : pdist z z ≤ 2 := by rw [pdist_self]; omega
    have d1 : pdist z (periodicLatticeShift z ν) ≤ 2 := by omega
    have d2 : pdist z (periodicLatticeShift z μ) ≤ 2 := by omega
    have d3 : pdist z (periodicLatticeShift (periodicLatticeShift z ν) μ) ≤ 2 := by omega
    have d4 : pdist z (periodicLatticeShift (periodicLatticeShift z μ) ν) ≤ 2 := by omega
    let p : PeriodicLatticePlaquette L := (z, ⟨(ν, μ), hνμ⟩)
    have hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, p, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact ⟨hmem z hz0, hmem _ d1⟩
      · exact ⟨hmem _ d1, hmem _ d3⟩
      · exact ⟨hmem _ d2, hmem _ d4⟩
      · exact ⟨hmem z hz0, hmem _ d2⟩
    obtain ⟨sites, i, hqΦ, hcb⟩ := hU.1.2 p hp
    obtain ⟨fΦ, hfΦ, hq⟩ := hqΦ
    obtain ⟨g, A, hA, hD, -⟩ := hU.2 fΦ sites i hfΦ hq
    have hbd : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e := hcb
    have e1 : CubeBond sites (z, ν) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    have e2 : CubeBond sites (periodicLatticeShift z ν, μ) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    have e3 : CubeBond sites (periodicLatticeShift z μ, ν) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    have e4 : CubeBond sites (z, μ) := hbd _ (by simp [periodicPlaquetteBoundaryEdges, p])
    -- the chart of the cube
    let K : CubeChart U (CubeBond sites) η (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)) :=
      { g := g, A := A, hA := fun e he => hA e he, hD := fun μ' ν' x h1 h2 => hD μ' ν' x h1 h2 }
    have hKg : K.g = g := rfl
    have hc1 : η * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) = a / (ell : ℝ) ^ i := by
      field_simp
    have hc2 : η ^ 2 * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)) = a / ((ell : ℝ) ^ i) ^ 2 := by
      field_simp
    have hpi : (1 : ℝ) ≤ (ell : ℝ) ^ i := one_le_pow₀ hellR
    have hsm : η * (a * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) ≤ 1 := by
      rw [hc1, div_le_one (by positivity)]; linarith
    have hcp := cube_plaq hη K hsm (z, ν, μ) ⟨e1, e2, e3, e4⟩
    rw [hKg, hc1, hc2] at hcp
    simp only at hcp
    rw [pw_gauge_dv] at hcp
    refine le_trans hcp ?_
    -- arithmetic: 2a/E + (4π+2)(a/e)^2 ≤ (4π+4) a / (ell^2)^(m-1), with E = e^2, e = ell^i, i ≥ m - 1
    have him : m - 1 ≤ i := by
      have := cube_index_ge hS hq e1.1 (hz (mem_Ball_self z 2)); omega
    have hE : ((ell : ℝ) ^ 2) ^ (m - 1) ≤ ((ell : ℝ) ^ i) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ hellR (by omega)
    have hpi2 : (0 : ℝ) < ((ell : ℝ) ^ i) ^ 2 := by positivity
    have hpiE : (0 : ℝ) < (ell : ℝ) ^ i := by positivity
    have hsq : (a / (ell : ℝ) ^ i) ^ 2 = a ^ 2 / ((ell : ℝ) ^ i) ^ 2 := by rw [div_pow]
    rw [hsq]
    have hpi0 := Real.pi_pos
    have hstep : 2 * (a / ((ell : ℝ) ^ i) ^ 2) + (4 * Real.pi + 2) * (a ^ 2 / ((ell : ℝ) ^ i) ^ 2)
        ≤ (4 * Real.pi + 4) * a / ((ell : ℝ) ^ i) ^ 2 := by
      have e5 : 2 * (a / ((ell : ℝ) ^ i) ^ 2) + (4 * Real.pi + 2) * (a ^ 2 / ((ell : ℝ) ^ i) ^ 2)
          = (2 * a + (4 * Real.pi + 2) * a ^ 2) / ((ell : ℝ) ^ i) ^ 2 := by ring
      rw [e5, div_le_div_iff_of_pos_right hpi2]
      have ha2 : a ^ 2 ≤ a := by nlinarith
      have h6 := mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi + 2)
      nlinarith
    refine le_trans hstep ?_
    exact div_le_div_of_nonneg_left (by positivity) hpos hE
  rcases lt_trichotomy ν μ with h | h | h
  · exact main ν μ h
  · subst h; rw [pw_self, dv_one]; exact hB0
  · rw [pw_swap, dv_inv]; exact main μ ν h

/-- every row read by `b ∈ bondsLam j` is analytic. -/
theorem classRows_readΦ {ell M R k bf : ℕ} {Fm : CF} [CubeFamOK Fm] {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hU : ClassCoupledHQ ell M Fm bf k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((bf : ℝ) * M * α₀))
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond (scaleUp ell k Lu)} (hb : b ∈ bondsLam (geomOf ell k S) j)
    {l : ℕ} {e : PeriodicLatticeEdge (scaleUp ell k Lu)} (hr : ReadRow ell j b l e) :
    ContDiffAt ℝ ⊤ (qStepComp (ell ^ l) ell (bgTower (geomOf ell k S) U l) e) 0 := by
  have hell0 : 0 < ell := by omega
  obtain ⟨ha0, ha1, hthr, hsmall⟩ := hsm
  set a : ℝ := (bf : ℝ) * M * α₀ with ha
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hlk : l ≤ k := by have := hr.1; omega
  have hdj : ∀ ρ : Fin 3, ell ^ j ∣ scaleUp ell k Lu ρ + 1 := scaleUp_dvd ell k hell0 Lu hjk
  set q0 : ℝ := (4 * Real.pi + 4) * a / (((ell : ℝ) ^ 2) ^ (j - 1 - 1)) with hq0
  have hpi : (0 : ℝ) < 4 * Real.pi + 4 := by have := Real.pi_pos; positivity
  have hq0n : 0 ≤ q0 := by positivity
  have hX : ((ell : ℝ) ^ 2) ^ l * q0 ≤ ((ell : ℝ) ^ 2) ^ 1 * ((4 * Real.pi + 4) * a) := by
    rw [hq0]; exact pow_ratio_le ell (by omega) _ (by positivity) (by have := hr.1; omega)
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have he6 : (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2) ^ 1 ≤ (ell : ℝ) ^ 6 := by
    rw [pow_one, ← pow_add]; exact pow_le_pow_right₀ hellR (by norm_num)
  have hX6 : (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ (ell : ℝ) ^ 6 * ((4 * Real.pi + 4) * a) := by
    calc (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * q0) ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ 1 * ((4 * Real.pi + 4) * a)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = ((ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2) ^ 1) * ((4 * Real.pi + 4) * a) := by ring
      _ ≤ (ell : ℝ) ^ 6 * ((4 * Real.pi + 4) * a) := mul_le_mul_of_nonneg_right he6 (by positivity)
  have he : e.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) := by
    have h := hr.2.1
    rw [mem_CoarseLattice] at h ⊢
    intro ν
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (Nat.dvd_of_mod_eq_zero (h ν)))
  refine qStepComp_contDiffAt_of_row _ _ _ _ ?_
  refine regRow_of_plaq ell hell U q0 hq0n l (scaleUp_dvd ell k hell0 Lu hlk) (scaleUp_big ell k hell Lu hT.2.1 hlk)
    ?_ ?_ e he ?_
  · nlinarith
  · nlinarith
  · intro z hz ν μ
    have := plaq_small_classΦ (L := scaleUp ell k Lu) (by omega) hη hS hU ha0 ha1 z
      (read_region hS hell hroom hj1 hjk hdj hb hr z hz) ν μ
    exact this

/-- **THE UNIT ROWS ARE ANALYTIC** for every `U` in the class: the rows `c` (`CRowIn ell Λ c`) at which `Q1jet` and
`C2tilde` read the unit-level averaging. -/
theorem classRows_unitΦ {ell M R k bf : ℕ} {Fm : CF} [CubeFamOK Fm] {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
    {Lam : Set (PeriodicLatticeSite Lu)} {α₀ : ℝ} {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hLam : LambdaOK2 ell M R k S Lam)
    (hU : ClassCoupledHQ ell M Fm bf k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((bf : ℝ) * M * α₀))
    (cb : CoarseBond Lu ell) (hc : CRowIn ell Lam cb) :
    ContDiffAt ℝ ⊤ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2)) 0 := by
  obtain ⟨ha0, ha1, hthr, hsmall⟩ := hsm
  set a : ℝ := (bf : ℝ) * M * α₀ with ha
  set V0 := unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k) with hV0
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  set q0 : ℝ := (4 * Real.pi + 4) * a / (((ell : ℝ) ^ 2) ^ (k - 1 - 1)) with hq0
  have hpi : (0 : ℝ) < 4 * Real.pi + 4 := by have := Real.pi_pos; positivity
  have hq0n : 0 ≤ q0 := by positivity
  have hX : ((ell : ℝ) ^ 2) ^ k * q0 ≤ ((ell : ℝ) ^ 2) ^ 2 * ((4 * Real.pi + 4) * a) := by
    rw [hq0]; exact pow_ratio_le ell (by omega) _ (by positivity) (by omega)
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have he6 : (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2) ^ 2 = (ell : ℝ) ^ 6 := by ring
  have hX6 : (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) ≤ (ell : ℝ) ^ 6 * ((4 * Real.pi + 4) * a) := by
    calc (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0) ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ 2 * ((4 * Real.pi + 4) * a)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = (ell : ℝ) ^ 6 * ((4 * Real.pi + 4) * a) := by rw [← he6]; ring
  -- the fine curvature tower at level `k`
  have hcurv := curv_tower_na_loc ell hell U q0 (fun z => ∀ ν μ : Fin 3, dv (pw 1 U z ν μ) ≤ q0) hq0n
    (fun y hy => hy) k (scaleUp_dvd ell k hell0 Lu le_rfl) (scaleUp_big ell k hell Lu hT.2.1 le_rfl) (by nlinarith)
  -- `Λ`-geometry
  obtain ⟨-, emb, hemb, -, hfar⟩ := hLam.1
  have hembY : ∀ y, emb y = embY ell k Lu hell0 y := fun y => funext (fun μ => Fin.ext (hemb y μ))
  have hy0 : ∃ y0 ∈ Lam, pdist y0 cb.1.1 ≤ ell := by
    rcases hc with h | h
    · exact ⟨cb.1.1, lamPrime_sub hell0 h, by rw [pdist_self]; exact Nat.zero_le _⟩
    · exact ⟨_, lamPrime_sub hell0 h, by rw [pdist_comm]; exact pdist_coarseShift_le _ _ _⟩
  obtain ⟨y0, hy0L, hy0d⟩ := hy0
  refine qStepComp_contDiffAt_of_row _ _ _ _ ?_
  intro x hx
  apply mem_LogReg_of_frob_lt
  show dv (loopVar 1 ell V0 (cb.1.1, cb.2) x) < r0
  rw [loopVar_eq_ladS 1 ell V0 (cb.1.1, cb.2) x hx]
  have hlen : (coarseGammaPath 1 cb.1.1 x).length ≤ 3 * ell := length_coarseGammaPath_le (show 0 < 1 by omega) hx
  refine lt_of_le_of_lt (ladS_le 1 V0 cb.2 ell (2 * (((ell : ℝ) ^ 2) ^ k * q0)) (coarseGammaPath 1 cb.1.1 x) cb.1.1 ?_) ?_
  · intro t ht
    rw [hV0, pw_unitBg]
    obtain ⟨b', hb', j', hj', hte⟩ := mem_ladPlaqs 1 cb.2 ell _ cb.1.1 t ht
    have h1 := pdist_pathBonds_le 1 _ cb.1.1 b' hb'
    have h2 : pdist b'.1 t.1 ≤ 1 * j' := by rw [hte]; exact pdist_coarseShift_le _ _ _
    have h3 := pdist_triangle cb.1.1 b'.1 t.1
    have h4 := pdist_triangle y0 cb.1.1 t.1
    have ht1 : pdist y0 t.1 ≤ 5 * ell := by
      have : 1 * (coarseGammaPath 1 cb.1.1 x).length ≤ 3 * ell := by omega
      omega
    -- the embedded ladder site is in `Ω_k`
    have hemk : embY ell k Lu hell0 t.1 ∈ S.Om k := by
      by_contra hn
      rw [← hembY] at hn
      have := hfar y0 hy0L t.1 hn
      omega
    have hemk' : embY ell k Lu hell0 t.1 ∈ S.Om ((k - 1) + 1) := by rw [Nat.sub_add_cancel hk]; exact hemk
    have hball := admissible_ball hS (j := k - 1) (by omega) hemk'
    have hroomk : 17 * ell ^ k ≤ R * (M * ell ^ (k - 1)) := by
      have e1 : ell ^ k = ell * ell ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      rw [e1]
      have := Nat.mul_le_mul_right (ell ^ (k - 1)) hroom
      calc 17 * (ell * ell ^ (k - 1)) = 17 * ell * ell ^ (k - 1) := by ring
        _ ≤ R * M * ell ^ (k - 1) := this
        _ = R * (M * ell ^ (k - 1)) := by ring
    have hrk := rhoT_le ell hell k
    have hgood : GoodPl ell (fun z => ∀ ν μ : Fin 3, dv (pw 1 U z ν μ) ≤ q0) k (embY ell k Lu hell0 t.1) := by
      refine goodPl_of_ball ell _ k _ (fun z hz ν μ => ?_)
      refine plaq_small_classΦ (L := scaleUp ell k Lu) (by omega) hη hS hU ha0 ha1 z ?_ ν μ
      refine le_trans (Ball_sub (y' := z) (d := pdist (embY ell k Lu hell0 t.1) z) le_rfl ?_) hball
      have hz' : pdist (embY ell k Lu hell0 t.1) z ≤ 2 * rhoT ell k := hz
      show pdist (embY ell k Lu hell0 t.1) z + 2 ≤ R * bigSide M ell (k - 1)
      unfold bigSide
      omega
    exact hcurv k le_rfl _ (embY_mem_CL ell k Lu hell0 t.1) hgood t.2.1 t.2.2
  · have hlR : ((coarseGammaPath 1 cb.1.1 x).length : ℝ) ≤ 3 * (ell : ℝ) := by exact_mod_cast (by omega)
    have hXn : 0 ≤ ((ell : ℝ) ^ 2) ^ k * q0 := by positivity
    calc ((coarseGammaPath 1 cb.1.1 x).length : ℝ) * ((ell : ℝ) * (2 * (((ell : ℝ) ^ 2) ^ k * q0)))
        ≤ (3 * (ell : ℝ)) * ((ell : ℝ) * (2 * (((ell : ℝ) ^ 2) ^ k * q0))) :=
          mul_le_mul_of_nonneg_right hlR (by positivity)
      _ = 6 * ((ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ k * q0)) := by ring
      _ ≤ 6 * ((ell : ℝ) ^ 6 * ((4 * Real.pi + 4) * a)) := by linarith
      _ < r0 := by nlinarith

end MXQ.ClassJets

#print axioms MXQ.ClassJets.classRows_unitΦ
#print axioms MXQ.ClassJets.classRows_readΦ
