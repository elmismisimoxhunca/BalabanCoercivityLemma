import CJ4

/-!
# CJ5 -- the unit level (`Q₁`, `C̃⁽²⁾`) and the headline-shaped corollary

* `pw_unitBg`: a unit plaquette of `unitBg (Ū^k)` IS the stride-`ell^k` plaquette of `Ū^k` at the embedded site.
* `classRows_unit`: for every row `c` with `CRowIn ell Λ c` (the rows `Q1jet`/`C2tilde` are read at), the component
  `qStepComp 1 ell (unitBg … (bgTower … U k)) (c₋, c.2)` is `C^∞` at `0`.
* `readRows_genuine_headline`: in the quantifier shape of the r8 headline block `P428Core8At` -- for `ell ≥ 2`, room
  `17 ell ≤ R M`, THERE IS `a₀ > 0` (witness: `classSmall_exists ell`) such that for every `k ≥ 1`, `Lu`, `α₀ > 0` with `c M α₀ ≤ a₀`,
  `TorusOK`, admissible `S`, `Λ` with `LambdaOK2`, `U` with `ClassCoupled`, every row the statement's jets read is genuine.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ClassJets

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist pcd Tower Admissible towerBj DescribedAt IsClassCube CubeBond HT bigSide scaleUp TorusOK
  LambdaOK LamPrime CRowIn)
open AdalyFormal.StatementLane2 (ClassCoupled PerCubeRegular2 CoversPlaqOm0c)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CurvBlock (dv pw ladS ladPlaqs pathBonds GoodPl curv_tower_na_loc loopVar_eq_ladS ladS_le mem_ladPlaqs)
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-! ## 1. the unit torus inside the fine torus -/

theorem embY_shift (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (y : PeriodicLatticeSite Lu) (ν : Fin 3) :
    embY ell k Lu hell (coarseShift y 1 ν) = coarseShift (embY ell k Lu hell y) (ell ^ k) ν := by
  funext σ
  apply Fin.ext
  by_cases h : σ = ν
  · subst h
    rw [embY_val, coarseShift_val_eq, coarseShift_val_eq, embY_val, scaleUp_succ ell k hell]
    have e1 : ell ^ k * (y σ).val + ell ^ k = ell ^ k * ((y σ).val + 1) := by ring
    rw [e1, mul_comm (Lu σ + 1) (ell ^ k), Nat.mul_mod_mul_left]
  · rw [embY_val, coarseShift_apply_ne _ _ _ _ h, coarseShift_apply_ne _ _ _ _ h, embY_val]

theorem pw_unitBg (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)) (y : PeriodicLatticeSite Lu) (ν μ : Fin 3) :
    pw 1 (unitBg ell k Lu hell V) y ν μ = pw (ell ^ k) V (embY ell k Lu hell y) ν μ := by
  unfold pw unitBg
  simp only
  rw [embY_shift, embY_shift]

theorem embY_mem_CL (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (y : PeriodicLatticeSite Lu) :
    embY ell k Lu hell y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
  rw [mem_CoarseLattice]; intro ν; rw [embY_val]; exact Nat.mul_mod_right _ _

/-! ## 2. the unit rows -/

/-- **THE UNIT ROWS ARE ANALYTIC** for every `U` in the class: the rows `c` (`CRowIn ell Λ c`) at which `Q1jet` and
`C2tilde` read the unit-level averaging. -/
theorem classRows_unit {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
    {Lam : Set (PeriodicLatticeSite Lu)} {α₀ : ℝ} {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hLam : LambdaOK2 ell M R k S Lam)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    (cb : CoarseBond Lu ell) (hc : CRowIn ell Lam cb) :
    ContDiffAt ℝ ⊤ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2)) 0 := by
  obtain ⟨ha0, ha1, hthr, hsmall⟩ := hsm
  set a : ℝ := (c : ℝ) * M * α₀ with ha
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
      refine plaq_small_class (L := scaleUp ell k Lu) (by omega) hη hS hU ha0 ha1 z ?_ ν μ
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

theorem classRows_unit_hasFDerivAt {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hLam : LambdaOK2 ell M R k S Lam)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    (cb : CoarseBond Lu ell) (hc : CRowIn ell Lam cb) :
    HasFDerivAt (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2))
      (fderiv ℝ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2)) 0) 0 :=
  ((classRows_unit hell0 hell hk hroom hS hT hLam hU hsm cb hc).differentiableAt (by simp)).hasFDerivAt

/-- companion of `AuditR8.QlinStepL_row_junk` at the unit level. -/
theorem classRows_unit_not_junk {ell M R k c : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {α₀ : ℝ}
    {U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)}
    (hell : 2 ≤ ell) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M) (hS : Admissible ell M R k S) (hT : TorusOK ell M Lu)
    (hLam : LambdaOK2 ell M R k S Lam)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : ClassSmall ell ((c : ℝ) * M * α₀))
    (cb : CoarseBond Lu ell) (hc : CRowIn ell Lam cb) :
    ¬ ¬ DifferentiableAt ℝ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2)) 0 :=
  fun h => h ((classRows_unit hell0 hell hk hroom hS hT hLam hU hsm cb hc).differentiableAt (by simp))

/-! ## 3. the headline-shaped corollary -/

/-- **ALL READ ROWS ARE GENUINE, in the quantifier shape of the r8 headline block.**  In the type `a₀` comes after
`(ell, M, R, c)` and BEFORE `k`, `Lu`, `α₀`, `S`, `Λ`, `U`; the witness used is `classSmall_exists ell` (a function of `ell`). -/
theorem readRows_genuine_headline (ell M R c : ℕ) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
        TorusOK ell M Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
        ∀ (U : PeriodicLinkConfiguration SU2 (scaleUp ell k Lu)), ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          (∀ j, 1 ≤ j → j ≤ k → ∀ b ∈ bondsLam (geomOf ell k S) j,
              Genuine ell (bgTower (geomOf ell k S) U) j b ∧
              ∀ l e, ReadRow ell j b l e →
                ContDiffAt ℝ ⊤ (qStepComp (ell ^ l) ell (bgTower (geomOf ell k S) U l) e) 0) ∧
          (∀ (hell0 : 0 < ell) (cb : CoarseBond Lu ell), CRowIn ell Lam cb →
              ContDiffAt ℝ ⊤ (qStepComp 1 ell (unitBg ell k Lu hell0 (bgTower (geomOf ell k S) U k)) (cb.1.1, cb.2)) 0) := by
  obtain ⟨a₀, ha₀, hsm⟩ := classSmall_exists ell
  refine ⟨a₀, ha₀, fun k hk Lu α₀ hα hsmall hT S hS Lam hLam U hU => ?_⟩
  have hcs : ClassSmall ell ((c : ℝ) * M * α₀) := hsm _ (by positivity) hsmall
  refine ⟨fun j hj1 hjk b hb => ⟨classRows_QlinB hell hroom hS hT hU hcs hj1 hjk hb,
    fun l e hr => classRows_read hell hroom hS hT hU hcs hj1 hjk hb hr⟩,
    fun hell0 cb hc => classRows_unit hell0 hell hk hroom hS hT hLam hU hcs cb hc⟩

#print axioms embY_shift
#print axioms pw_unitBg
#print axioms classRows_unit
#print axioms classRows_unit_hasFDerivAt
#print axioms classRows_unit_not_junk
#print axioms readRows_genuine_headline

end AdalyFormal.ClassJets
