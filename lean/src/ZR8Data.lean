import ZR8DataB

/-!
# ZR8Data -- r8 LOCALITY THEOREM for the repaired statement: every ingredient of `genForm`/`genC`/`WellDef` reads `U` only on the
bonds with both endpoints in `Ω₀`

Hypotheses (`LocHyp`): `S` admissible (`Admissible ell M R k S`), `1 ≤ k`, `2 ≤ ell`, room `17 ell ≤ R M`, `Λ` with `LambdaOK2`.
Two configurations `U, U'` that agree on every `BothIn Ω₀` bond.  Conclusions (each a kernel theorem below):
 * `QfullOf_congr`, `C2fullOf_congr_U`, `C2fullOf_congr_in`, `sector_congr` (bond sector, rows `j ≥ 1` read `U` within `2 rhoT j`);
 * `data_congr` : the whole base data `(Δ_π, T, T*, Q, Q*, Q*aQ, C^{(2)}_π, J)` of (3.122)-(3.128) is THE SAME;
 * `G1inv_congr`, `Qin_congr`, `G1in_congr`, `H1in_congr`, `Nmat_congr`, `firstTerm_congr`;
 * unit level: `unitBgU_agree` (on the unit sites within `5 ell` of `Λ`), `Q1_rows_congr`, `C2tilde_rows_congr` (rows `c ∈ Dset`),
   `H0_congr`, `Cop_congr`, `D2in_congr`;
 * `genForm_congr_outside` : `genForm_U(C_U B̃) = genForm_{U'}(C_{U'} B̃)`, `genC_congr`, `WellDef_congr`, `GuardsUnit_congr`,
   `WellDefG_congr`, `InstIneq_congr`, `InstAtWD_congr`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace AdalyFormal.StatementLaneR8

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-! ## 3. the unit level -/

theorem lamPrime_sub {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell) {Lam : Set (PeriodicLatticeSite Lu)}
    {y : PeriodicLatticeSite Lu} (hy : y ∈ LamPrime ell Lam) : y ∈ Lam :=
  hy.2 y (mem_blockOf.mpr (fun μ => ⟨le_rfl, by omega⟩))

/-- the unit sites within `5 ell` of a row `c ∈ Dset` embed into `Ω_k`. -/
theorem unit_row_emb {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    {Lam : Set (PeriodicLatticeSite Lu)} (h : LocHyp ell M R k S Lam) {c : CoarseBond Lu ell} (hc : CRowIn ell Lam c)
    {z : PeriodicLatticeSite Lu} (hz : z ∈ Ball c.1.1 (4 * (1 * ell))) :
    embY ell k Lu (by have := h.hell; omega) z ∈ S.Om k := by
  obtain ⟨-, emb, hemb, -, hfar⟩ := h.lam.1
  have hembY : ∀ y, emb y = embY ell k Lu (by have := h.hell; omega) y := fun y => funext (fun μ => Fin.ext (hemb y μ))
  have hell0 : 0 < ell := by have := h.hell; omega
  by_contra hn
  rw [← hembY] at hn
  have hroom := h.room
  rcases hc with hc | hc
  · have := hfar c.1.1 (lamPrime_sub hell0 hc) z hn
    have hz' : pdist c.1.1 z ≤ 4 * (1 * ell) := hz
    omega
  · have := hfar _ (lamPrime_sub hell0 hc) z hn
    have h1 : pdist (coarseShift c.1.1 ell c.2) c.1.1 ≤ ell := by rw [pdist_comm]; exact pdist_coarseShift_le _ _ _
    have h2 := pdist_triangle (coarseShift c.1.1 ell c.2) c.1.1 z
    have hz' : pdist c.1.1 z ≤ 4 * (1 * ell) := hz
    omega

theorem unitBgU_agree (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e)
    {c : CoarseBond P.Lu P.ell} (hc : CRowIn P.ell P.Lam c) :
    AgreeAt (Ball c.1.1 (4 * (1 * P.ell))) P.unitBgU ({ P with U := U' } : IngrBParams).unitBgU := by
  intro z hz μ
  have hemb := unit_row_emb h hc hz
  show bgTower P.G P.U P.k (embY P.ell P.k P.Lu P.hell z, μ) = bgTower P.G U' P.k (embY P.ell P.k P.Lu P.hell z, μ)
  refine bgTower_congr P.G (by have := h.hell; show 0 < P.ell; omega) P.k _ (agreeAt_of_both hUU ?_) μ
  have hk := h.hk
  have hr := room_arith h.hell h.room (j := P.k) hk
  refine le_trans (Ball_mono ?_) (admissible_ball_Om0 h.adm hk (by omega) hemb)
  show rhoT P.ell P.k + 1 ≤ R * (M * P.ell ^ (P.k - 1))
  omega

theorem suCoordFInv_apply_congr {Lx : PeriodicLatticeExtent} {x x' : XS Lx} {b : Bond Lx} (h : x b = x' b) :
    suCoordFInv x b = suCoordFInv x' b := by
  apply Subtype.ext
  show toM2 (x b) = toM2 (x' b)
  rw [h]

theorem Q1_rows_congr (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e)
    (B : Bond P.Lu → SuTwo) {c : CoarseBond P.Lu P.ell} (hc : CRowIn P.ell P.Lam c) :
    ({ P with U := U' } : IngrBParams).Q1 B c = P.Q1 B c := by
  have hrow : QlinStepL 1 P.ell ({ P with U := U' } : IngrBParams).unitBgU (suCoordF B) (c.1.1, c.2)
      = QlinStepL 1 P.ell P.unitBgU (suCoordF B) (c.1.1, c.2) :=
    QlinStepL_congr_bg 1 P.ell one_pos (c.1.1, c.2) (unitBgU_agree P h U' hUU hc).symm _
  show ((P.ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 P.ell ({ P with U := U' } : IngrBParams).unitBgU (suCoordF B))) (c.1.1, c.2)
    = ((P.ell : ℝ)⁻¹) • (suCoordFInv (QlinStepL 1 P.ell P.unitBgU (suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_apply_congr hrow]

theorem C2tilde_rows_congr (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e)
    (B : Bond P.Lu → SuTwo) {c : CoarseBond P.Lu P.ell} (hc : CRowIn P.ell P.Lam c) :
    C2tilde P.ell ({ P with U := U' } : IngrBParams).unitBgU B c = C2tilde P.ell P.unitBgU B c := by
  have hrow : C2StepL 1 P.ell ({ P with U := U' } : IngrBParams).unitBgU (suCoordF B) (c.1.1, c.2)
      = C2StepL 1 P.ell P.unitBgU (suCoordF B) (c.1.1, c.2) :=
    C2StepL_congr_bg 1 P.ell one_pos (c.1.1, c.2) (unitBgU_agree P h U' hUU hc).symm _
  show (suCoordFInv (C2StepL 1 P.ell ({ P with U := U' } : IngrBParams).unitBgU (suCoordF B))) (c.1.1, c.2)
    = (suCoordFInv (C2StepL 1 P.ell P.unitBgU (suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_apply_congr hrow]

theorem H0_congr_rows {Lu : PeriodicLatticeExtent} {ell : ℕ} (Lam : Set (PeriodicLatticeSite Lu))
    {Q Q' : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)}
    (h : ∀ B c, CRowIn ell Lam c → Q B c = Q' B c) : H0 Lam Q = H0 Lam Q' := by
  refine LinearMap.ext (fun w => funext (fun c => ?_))
  exact h _ c.1 c.2

theorem rhoD_congr_rows {Lu : PeriodicLatticeExtent} {ell : ℕ} (Lam : Set (PeriodicLatticeSite Lu))
    {f f' : CoarseBond Lu ell → SuTwo} (h : ∀ c, CRowIn ell Lam c → f c = f' c) : rhoD ell Lam f = rhoD ell Lam f' :=
  funext (fun c => h c.1 c.2)

theorem hLift_congr_rows {Lu : PeriodicLatticeExtent} {ell : ℕ} (Lam : Set (PeriodicLatticeSite Lu))
    {Q Q' : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)}
    (h : ∀ B c, CRowIn ell Lam c → Q B c = Q' B c) {f f' : CoarseBond Lu ell → SuTwo}
    (hf : ∀ c, CRowIn ell Lam c → f c = f' c) : hLift Lam Q f = hLift Lam Q' f' := by
  have hH0 := H0_congr_rows Lam h
  have hH : H0inv Lam Q = H0inv Lam Q' := by
    unfold H0inv
    split_ifs with h1 h2 h2
    · refine LinearMap.ext (fun w => h2.1 ?_)
      have e1 : H0 Lam Q' ((LinearEquiv.ofBijective (H0 Lam Q) h1).symm w) = w := by
        rw [← hH0]; exact (LinearEquiv.ofBijective (H0 Lam Q) h1).apply_symm_apply w
      have e2 : H0 Lam Q' ((LinearEquiv.ofBijective (H0 Lam Q') h2).symm w) = w :=
        (LinearEquiv.ofBijective (H0 Lam Q') h2).apply_symm_apply w
      exact e1.trans e2.symm
    · exact absurd (hH0 ▸ h1) h2
    · exact absurd (hH0 ▸ h2) h1
    · rfl
  show iotaD ell Lam (H0inv Lam Q (rhoD ell Lam f)) = iotaD ell Lam (H0inv Lam Q' (rhoD ell Lam f'))
  rw [hH, rhoD_congr_rows Lam hf]

theorem Cop_congr_rows {Lu : PeriodicLatticeExtent} {ell : ℕ} (Lam : Set (PeriodicLatticeSite Lu))
    {Q Q' : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo)}
    (h : ∀ B c, CRowIn ell Lam c → Q B c = Q' B c) : Cop Lam Q = Cop Lam Q' := by
  refine LinearMap.ext (fun B => ?_)
  show B - hLift Lam Q (Q B) = B - hLift Lam Q' (Q' B)
  rw [hLift_congr_rows Lam h (fun c hc => h B c hc)]

/-! ## 4. the genuine claim -/

theorem genC_congr (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    GenP.genC ({ P with U := U' } : IngrBParams) = GenP.genC P :=
  Cop_congr_rows P.Lam (fun B c hc => Q1_rows_congr P h U' hUU B hc)

theorem D2in_congr (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    ({ P with U := U' } : IngrBParams).D2in = P.D2in := by
  funext B
  show WithLp.toLp 2 (((P.ell : ℝ)⁻¹) • hLift P.Lam ({ P with U := U' } : IngrBParams).Q1
      (C2tilde P.ell ({ P with U := U' } : IngrBParams).unitBgU (WithLp.ofLp B)))
    = WithLp.toLp 2 (((P.ell : ℝ)⁻¹) • hLift P.Lam P.Q1 (C2tilde P.ell P.unitBgU (WithLp.ofLp B)))
  rw [hLift_congr_rows P.Lam (fun B c hc => Q1_rows_congr P h U' hUU B hc)
    (fun c hc => C2tilde_rows_congr P h U' hUU _ hc)]

theorem WellDef_congr (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    GenP.WellDef ({ P with U := U' } : IngrBParams) ↔ GenP.WellDef P := by
  have hH : H0 P.Lam ({ P with U := U' } : IngrBParams).Q1 = H0 P.Lam P.Q1 :=
    H0_congr_rows P.Lam (fun B c hc => Q1_rows_congr P h U' hUU B hc)
  have hd := data_congr P h.adm h.hell h.room U' hUU
  have hg := G1inv_congr P h.adm h.hell h.room U' hUU
  unfold GenP.WellDef GenP.Nmat
  rw [hH, hg, hd]

theorem genForm_congr_outside (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) (Bt : Bond P.Lu → SuTwo) :
    GenP.genForm ({ P with U := U' } : IngrBParams) (WithLp.toLp 2 (GenP.genC ({ P with U := U' } : IngrBParams) Bt))
      = GenP.genForm P (WithLp.toLp 2 (GenP.genC P Bt)) := by
  have hd := data_congr P h.adm h.hell h.room U' hUU
  have hg := G1inv_congr P h.adm h.hell h.room U' hUU
  have hJ := Jf_congr_outside P U' hUU
  have hD2 := D2in_congr P h U' hUU
  rw [genC_congr P h U' hUU]
  unfold GenP.genForm GenP.firstTerm GenP.Nmat IngrBParams.H1in
  rw [hd, hg, hJ, hD2]
  rfl

theorem GuardsUnit_congr (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    GenP.GuardsUnit ({ P with U := U' } : IngrBParams) ↔ GenP.GuardsUnit P := by
  have hd := data_congr P h.adm h.hell h.room U' hUU
  have hDel := DelpA_congr h.adm h.hell h.room hUU P.a
  unfold GenP.GuardsUnit
  rw [hd]
  show (IsUnit (DelpA P.G U' P.a + (1 - siteMask P.G.Om0)) ∧ _) ↔ _
  rw [← hDel]

theorem WellDefG_congr (P : IngrBParams) {M R : ℕ} (h : LocHyp P.ell M R P.k P.S P.Lam)
    (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    GenP.WellDefG ({ P with U := U' } : IngrBParams) ↔ GenP.WellDefG P := by
  unfold GenP.WellDefG
  rw [WellDef_congr P h U' hUU, GuardsUnit_congr P h U' hUU]

/-- **THE LOCALITY THEOREM AT THE STATEMENT'S CONCLUSION.**  Under the tower/`Λ` hypotheses, the printed inequality at `U` and
at any `U'` agreeing with `U` on the `BothIn Ω₀` bonds are the same proposition. -/
theorem InstIneq_congr {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R : ℕ} (h : LocHyp ell M R k S Lam)
    {U U' : Cfg (scaleUp ell k Lu)} (hUU : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U e = U' e) :
    InstIneq ell k hell0 a Lu γ₀ S Lam U ↔ InstIneq ell k hell0 a Lu γ₀ S Lam U' := by
  have hg : ∀ Bt : Bond Lu → SuTwo,
      GenP.genForm (gparams ell k Lu hell0 S U' a Lam) (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U' a Lam) Bt))
        = GenP.genForm (gparams ell k Lu hell0 S U a Lam) (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S U a Lam) Bt)) :=
    genForm_congr_outside (gparams ell k Lu hell0 S U a Lam) h U' hUU
  unfold InstIneq
  constructor
  · intro H Bt h1 h2; rw [hg Bt]; exact H Bt h1 h2
  · intro H Bt h1 h2; rw [← hg Bt]; exact H Bt h1 h2

theorem InstAtWD_congr {ell k : ℕ} (hell0 : 0 < ell) (a : ℝ) {Lu : PeriodicLatticeExtent} (γ₀ : ℝ)
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {M R : ℕ} (h : LocHyp ell M R k S Lam)
    {U U' : Cfg (scaleUp ell k Lu)} (hUU : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U e = U' e) :
    InstAtWD ell k hell0 a Lu γ₀ S Lam U ↔ InstAtWD ell k hell0 a Lu γ₀ S Lam U' := by
  unfold InstAtWD
  rw [InstIneq_congr hell0 a γ₀ h hUU]
  have := WellDefG_congr (gparams ell k Lu hell0 S U a Lam) h U' hUU
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨this.mpr h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨this.mp h1, h2⟩

#print axioms unitBgU_agree
#print axioms Q1_rows_congr
#print axioms C2tilde_rows_congr
#print axioms genC_congr
#print axioms D2in_congr
#print axioms WellDef_congr
#print axioms genForm_congr_outside
#print axioms GuardsUnit_congr
#print axioms WellDefG_congr
#print axioms InstIneq_congr
#print axioms InstAtWD_congr


end AdalyFormal.StatementLaneR8
