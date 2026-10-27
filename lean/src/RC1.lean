import CJ8

/-!
# RC1 -- the r8 statement as a function of its JETS, and the TOP-LEVEL read set

The r8 statement (`GenP.genForm`, `GenP.genC`, `GenP.WellDef`, `GenP.GuardsUnit`) reads the averaging jets through exactly four
objects: the level composites `QlinCompL` (first order) and `D2CompL` (second order, bilinear) of the bond sector, and the
unit-level one-step jets `QlinStepL 1` and `D2StepL 1`.  This module abstracts those four objects into a `TopJets` record and
re-builds every statement object from an ARBITRARY record (`QfullJ`, `C2fullJ`, `sectorJ`, `Q1J`, `C2tJ`, `GenS.*`, `genFormT`, ...),
each a verbatim copy of the r8 definition with the jet replaced by the record field.

* `genForm_eq_T`, `genC_eq_T`, `WellDef_iff_T`, `GuardsUnit_iff_T` : the r8 objects ARE the generic ones at the r8 record
  `r8Top P` (definitional, `rfl`).
* `readTop_complete` (**top-level read set**): two records that agree on the rows
  - `(j, b)` with `j ≤ k`, `b ∈ bondsLam j` (first order `∀ v`, second order on the diagonal `∀ v`), and
  - unit rows `(c₋, c.2)` with `CRowIn ell Λ c` (same),
  give the same `genFormT`, `genCT`, `WellDefT`, `GuardsUnitT`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ReadsetComplete

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower CRowIn)
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

variable {L : PeriodicLatticeExtent}

/-! ## 1. the bond sector from arbitrary level jets -/

/-- `QlinB` with the level jet `QC j` in place of `QlinCompL G.ell (bgTower G U) j`. -/
noncomputable def QlinBJ (QC : ℕ → (XS L →L[ℝ] XS L)) (j : ℕ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    (suCoordInv ∘ₗ ((QC j : XS L →L[ℝ] XS L) : XS L →ₗ[ℝ] XS L) ∘ₗ suCoord)

/-- `D2B` with the bilinear level jet `DC j`. -/
noncomputable def D2BJ (DC : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) (j : ℕ) :
    BondFnL2 L →ₗ[ℝ] BondFnL2 L →ₗ[ℝ] BondFnL2 L :=
  LinearMap.mk₂ ℝ
    (fun A B => suCoordInv (DC j (suCoord A) (suCoord B)))
    (fun A A' B => by simp)
    (fun c A B => by simp)
    (fun A B B' => by simp)
    (fun c A B => by simp)

noncomputable def C2rawBJ (DC : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) (j : ℕ) (A : BondFnL2 L) : BondFnL2 L :=
  (1 / 2 : ℝ) • D2BJ DC j A A

/-- `QfullOf` with `QlinBJ`. -/
noncomputable def QfullJ (G : TowerGeom L) (QC : ℕ → (XS L →L[ℝ] XS L)) : BondFnL2 L →L[ℝ] FSp G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => WithLp.toLp 2 (fun p : BIdx G =>
        (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinBJ QC p.1 A)) p.2.1)
      map_add' := fun A A' => by
        refine PiLp.ext (fun p => ?_); simp [smul_add]
      map_smul' := fun c A => by
        refine PiLp.ext (fun p => ?_)
        simp only [map_smul, PiLp.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }

/-- `C2fullOf` with `C2rawBJ`. -/
noncomputable def C2fullJ (G : TowerGeom L) (DC : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) (A : BondFnL2 L) : FSp G :=
  WithLp.toLp 2 (fun p : BIdx G =>
    (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawBJ DC p.1 A)) p.2.1)

theorem C2fullJ_quad (G : TowerGeom L) (DC : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) : IsQuadMap (C2fullJ G DC) := by
  refine ⟨LinearMap.mk₂ ℝ
    (fun A B => WithLp.toLp 2 (fun p : BIdx G =>
      (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp ((1 / 2 : ℝ) • D2BJ DC p.1 A B)) p.2.1))
    (fun A A' B => by refine PiLp.ext (fun p => ?_); simp [smul_add])
    (fun c A B => by
      refine PiLp.ext (fun p => ?_); simp only [map_smul, LinearMap.smul_apply, PiLp.smul_apply]
      simp only [smul_smul]; congr 1; ring)
    (fun A B B' => by refine PiLp.ext (fun p => ?_); simp [smul_add])
    (fun c A B => by
      refine PiLp.ext (fun p => ?_); simp only [map_smul, PiLp.smul_apply]
      simp only [smul_smul]; congr 1; ring), fun A => ?_⟩
  refine PiLp.ext (fun p => ?_)
  simp [C2fullJ, C2rawBJ]

/-- the bond sector built from arbitrary level jets. -/
noncomputable def sectorJ (G : TowerGeom L) (QC : ℕ → (XS L →L[ℝ] XS L))
    (DC : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) : BondSector G where
  Qfull := QfullJ G QC
  C2full := C2fullJ G DC
  C2_quad := C2fullJ_quad G DC

/-- **the r8 bond sector IS `sectorJ` at the r8 level jets** (definitional). -/
theorem bondSectorOf_eq_J (G : TowerGeom L) (U : Cfg L) :
    bondSectorOf G U = sectorJ G (QlinCompL G.ell (bgTower G U)) (D2CompL G.ell (bgTower G U)) := rfl

/-- **bond-sector read set.**  `sectorJ` reads the level jets only at rows `(j, b)`, `j ≤ G.k`, `b ∈ bondsLam G j` (first order:
every input; second order: the diagonal). -/
theorem sectorJ_congr (G : TowerGeom L) {QC QC' : ℕ → (XS L →L[ℝ] XS L)} {DC DC' : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)}
    (hQ : ∀ j b, j ≤ G.k → b ∈ bondsLam G j → ∀ v, QC j v b = QC' j v b)
    (hD : ∀ j b, j ≤ G.k → b ∈ bondsLam G j → ∀ v, DC j v v b = DC' j v v b) :
    sectorJ G QC DC = sectorJ G QC' DC' := by
  have h1 : QfullJ G QC = QfullJ G QC' := by
    ext1 A
    refine PiLp.ext (fun p => ?_)
    show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinBJ QC p.1 A)) p.2.1
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinBJ QC' p.1 A)) p.2.1
    congr 1
    exact suCoordInv_apply_congr (hQ p.1 p.2.1 (Nat.lt_succ_iff.mp p.1.2) p.2.2 (suCoord A))
  have h2 : C2fullJ G DC = C2fullJ G DC' := by
    funext A
    refine PiLp.ext (fun p => ?_)
    show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp ((1 / 2 : ℝ) • suCoordInv (DC p.1 (suCoord A) (suCoord A)))) p.2.1
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp ((1 / 2 : ℝ) • suCoordInv (DC' p.1 (suCoord A) (suCoord A)))) p.2.1
    simp only [WithLp.ofLp_smul, Pi.smul_apply]
    congr 2
    exact suCoordInv_apply_congr (hD p.1 p.2.1 (Nat.lt_succ_iff.mp p.1.2) p.2.2 (suCoord A))
  unfold sectorJ
  congr 1

/-! ## 2. the unit level from arbitrary one-step jets -/

/-- `Q1jet` with the unit one-step jet `T` in place of `QlinStepL 1 ell V0`. -/
noncomputable def Q1J {Lu : PeriodicLatticeExtent} (ell : ℕ) (T : XS Lu →L[ℝ] XS Lu) :
    (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo) where
  toFun B := fun c => ((ell : ℝ)⁻¹) • (suCoordFInv (T (suCoordF B))) (c.1.1, c.2)
  map_add' A B := by funext c; simp [smul_add]
  map_smul' r A := by
    funext c
    simp only [RingHom.id_apply, Pi.smul_apply, map_smul]
    exact smul_comm ((ell : ℝ)⁻¹) r _

/-- `C2tilde` with the bilinear unit jet `D` (`C2StepL = ½ D2StepL a a`). -/
noncomputable def C2tJ {Lu : PeriodicLatticeExtent} (ell : ℕ) (D : XS Lu →ₗ[ℝ] XS Lu →ₗ[ℝ] XS Lu)
    (B : Bond Lu → SuTwo) : CoarseBond Lu ell → SuTwo := fun c =>
  (suCoordFInv ((1 / 2 : ℝ) • D (suCoordF B) (suCoordF B))) (c.1.1, c.2)

theorem Q1jet_eq_J {Lu : PeriodicLatticeExtent} (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 Lu) :
    Q1jet ell V0 = Q1J ell (QlinStepL 1 ell V0) := rfl

theorem C2tilde_eq_J {Lu : PeriodicLatticeExtent} (ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 Lu) :
    C2tilde ell V0 = C2tJ ell (D2StepL 1 ell V0) := rfl

theorem suCoordFInv_row {Lx : PeriodicLatticeExtent} {x x' : XS Lx} {b : Bond Lx} (h : x b = x' b) :
    suCoordFInv x b = suCoordFInv x' b := suCoordFInv_apply_congr h

/-- **unit read set (first order).** -/
theorem Q1J_rows {Lu : PeriodicLatticeExtent} (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu)) {T T' : XS Lu →L[ℝ] XS Lu}
    (h : ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → ∀ v, T v (c.1.1, c.2) = T' v (c.1.1, c.2)) :
    ∀ B c, CRowIn ell Lam c → Q1J ell T B c = Q1J ell T' B c := by
  intro B c hc
  show ((ell : ℝ)⁻¹) • (suCoordFInv (T (suCoordF B))) (c.1.1, c.2) = ((ell : ℝ)⁻¹) • (suCoordFInv (T' (suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_row (h c hc (suCoordF B))]

/-- **unit read set (second order, diagonal).** -/
theorem C2tJ_rows {Lu : PeriodicLatticeExtent} (ell : ℕ) (Lam : Set (PeriodicLatticeSite Lu))
    {D D' : XS Lu →ₗ[ℝ] XS Lu →ₗ[ℝ] XS Lu}
    (h : ∀ c : CoarseBond Lu ell, CRowIn ell Lam c → ∀ v, D v v (c.1.1, c.2) = D' v v (c.1.1, c.2)) :
    ∀ B c, CRowIn ell Lam c → C2tJ ell D B c = C2tJ ell D' B c := by
  intro B c hc
  show (suCoordFInv ((1 / 2 : ℝ) • D (suCoordF B) (suCoordF B))) (c.1.1, c.2)
    = (suCoordFInv ((1 / 2 : ℝ) • D' (suCoordF B) (suCoordF B))) (c.1.1, c.2)
  refine suCoordFInv_row ?_
  show (1 / 2 : ℝ) • D (suCoordF B) (suCoordF B) (c.1.1, c.2) = (1 / 2 : ℝ) • D' (suCoordF B) (suCoordF B) (c.1.1, c.2)
  rw [h c hc (suCoordF B)]

/-! ## 3. every statement object from (sector, `Q₁`, `C̃⁽²⁾`) -/

namespace GenS
variable (P : IngrBParams)

noncomputable def dataS (Sct : BondSector P.G) :
    BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  baseData P.G P.U P.a Sct P.Jf

theorem dataS_laws (Sct : BondSector P.G) : (dataS P Sct).Laws := baseData_laws P.G P.U P.a Sct P.Jf

noncomputable def G1invS (Sct : BondSector P.G) : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  Classical.choose ((dataS P Sct).exists_G1inv (dataS_laws P Sct))

noncomputable def NmatS (Sct : BondSector P.G) : FSp P.G →L[ℝ] FSp P.G :=
  ((dataS P Sct).Q.comp ((dataS P Sct).G1 (G1invS P Sct))).comp (dataS P Sct).Qs

noncomputable def firstTermS (Sct : BondSector P.G) (B : BondFnL2 P.Lu) : ℝ :=
  P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (NmatS P Sct) (ContinuousLinearMap.adjoint P.tau B)⟫

noncomputable def H1inS (Sct : BondSector P.G) : BondFnL2 P.Lu →L[ℝ] BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  (iE P.G).comp (((dataS P Sct).H1 (G1invS P Sct)).comp (ContinuousLinearMap.adjoint P.tau))

noncomputable def D2inS (Q1 : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo))
    (C2t : (Bond P.Lu → SuTwo) → CoarseBond P.Lu P.ell → SuTwo) (B : BondFnL2 P.Lu) : BondFnL2 P.Lu :=
  WithLp.toLp 2 (((P.ell : ℝ)⁻¹) • hLift P.Lam Q1 (C2t (WithLp.ofLp B)))

noncomputable def genFormS (Sct : BondSector P.G) (Q1 : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo))
    (C2t : (Bond P.Lu → SuTwo) → CoarseBond P.Lu P.ell → SuTwo) (B : BondFnL2 P.Lu) : ℝ :=
  firstTermS P Sct B - P.a * ⟪B, B⟫ - 2 * ⟪H1inS P Sct (D2inS P Q1 C2t B), P.Jf⟫

noncomputable def genCS (Q1 : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo)) :
    (Bond P.Lu → SuTwo) →ₗ[ℝ] (Bond P.Lu → SuTwo) := Cop P.Lam Q1

def WellDefS (Sct : BondSector P.G) (Q1 : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo)) : Prop :=
  Function.Bijective (H0 P.Lam Q1) ∧ IsUnit (G1invS P Sct) ∧ IsUnit (NmatS P Sct)

def GuardsUnitS (Sct : BondSector P.G) : Prop :=
  IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)) ∧ IsUnit (dataS P Sct).Ginv ∧
    IsUnit (((dataS P Sct).Q.comp (dataS P Sct).G).comp (dataS P Sct).Qs)

/-- the r8 objects are the generic ones at (`P.sector`, `P.Q1`, `C2tilde P.ell P.unitBgU`) (definitional). -/
theorem genForm_eq_S (B : BondFnL2 P.Lu) :
    GenP.genForm P B = genFormS P P.sector P.Q1 (C2tilde P.ell P.unitBgU) B := rfl

theorem genC_eq_S : GenP.genC P = genCS P P.Q1 := rfl

theorem WellDef_iff_S : GenP.WellDef P ↔ WellDefS P P.sector P.Q1 := Iff.rfl

theorem GuardsUnit_iff_S : GenP.GuardsUnit P ↔ GuardsUnitS P P.sector := Iff.rfl

/-- **unit read set of every statement object**: only the `CRowIn` rows of `Q₁` and `C̃⁽²⁾` are read. -/
theorem genFormS_congr (Sct : BondSector P.G) {Q1 Q1' : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo)}
    {C2t C2t' : (Bond P.Lu → SuTwo) → CoarseBond P.Lu P.ell → SuTwo}
    (hQ : ∀ B c, CRowIn P.ell P.Lam c → Q1 B c = Q1' B c) (hC : ∀ B c, CRowIn P.ell P.Lam c → C2t B c = C2t' B c)
    (B : BondFnL2 P.Lu) : genFormS P Sct Q1 C2t B = genFormS P Sct Q1' C2t' B := by
  have hD : D2inS P Q1 C2t B = D2inS P Q1' C2t' B := by
    unfold D2inS
    rw [hLift_congr_rows P.Lam hQ (fun c hc => hC _ c hc)]
  unfold genFormS
  rw [hD]

theorem genCS_congr {Q1 Q1' : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo)}
    (hQ : ∀ B c, CRowIn P.ell P.Lam c → Q1 B c = Q1' B c) : genCS P Q1 = genCS P Q1' :=
  Cop_congr_rows P.Lam hQ

theorem WellDefS_congr (Sct : BondSector P.G) {Q1 Q1' : (Bond P.Lu → SuTwo) →ₗ[ℝ] (CoarseBond P.Lu P.ell → SuTwo)}
    (hQ : ∀ B c, CRowIn P.ell P.Lam c → Q1 B c = Q1' B c) : WellDefS P Sct Q1 ↔ WellDefS P Sct Q1' := by
  unfold WellDefS
  rw [H0_congr_rows P.Lam hQ]

end GenS

/-! ## 4. top-level jet records -/

/-- the four jet objects the statement reads. -/
structure TopJets (Lf Lu : PeriodicLatticeExtent) where
  QC : ℕ → (XS Lf →L[ℝ] XS Lf)
  DC : ℕ → (XS Lf →ₗ[ℝ] XS Lf →ₗ[ℝ] XS Lf)
  QU : XS Lu →L[ℝ] XS Lu
  DU : XS Lu →ₗ[ℝ] XS Lu →ₗ[ℝ] XS Lu

/-- the r8 record. -/
noncomputable def r8Top (P : IngrBParams) : TopJets (scaleUp P.ell P.k P.Lu) P.Lu where
  QC := QlinCompL P.G.ell (bgTower P.G P.U)
  DC := D2CompL P.G.ell (bgTower P.G P.U)
  QU := QlinStepL 1 P.ell P.unitBgU
  DU := D2StepL 1 P.ell P.unitBgU

section
variable (P : IngrBParams) (T : TopJets (scaleUp P.ell P.k P.Lu) P.Lu)

noncomputable def sectorT : BondSector P.G := sectorJ P.G T.QC T.DC
noncomputable def genFormT (B : BondFnL2 P.Lu) : ℝ :=
  GenS.genFormS P (sectorT P T) (Q1J P.ell T.QU) (C2tJ P.ell T.DU) B
noncomputable def genCT : (Bond P.Lu → SuTwo) →ₗ[ℝ] (Bond P.Lu → SuTwo) := GenS.genCS P (Q1J P.ell T.QU)
def WellDefT : Prop := GenS.WellDefS P (sectorT P T) (Q1J P.ell T.QU)
def GuardsUnitT : Prop := GenS.GuardsUnitS P (sectorT P T)
def WellDefGT : Prop := WellDefT P T ∧ GuardsUnitT P T
end

theorem genForm_eq_T (P : IngrBParams) (B : BondFnL2 P.Lu) : GenP.genForm P B = genFormT P (r8Top P) B := rfl
theorem genC_eq_T (P : IngrBParams) : GenP.genC P = genCT P (r8Top P) := rfl
theorem WellDef_iff_T (P : IngrBParams) : GenP.WellDef P ↔ WellDefT P (r8Top P) := Iff.rfl
theorem GuardsUnit_iff_T (P : IngrBParams) : GenP.GuardsUnit P ↔ GuardsUnitT P (r8Top P) := Iff.rfl
theorem WellDefG_iff_T (P : IngrBParams) : GenP.WellDefG P ↔ WellDefGT P (r8Top P) := Iff.rfl

/-- **the top-level read set**: bond-sector rows `(j ≤ k, b ∈ bondsLam j)` and unit rows `CRowIn`. -/
def AgreeTop (P : IngrBParams) (T T' : TopJets (scaleUp P.ell P.k P.Lu) P.Lu) : Prop :=
  (∀ j b, j ≤ P.G.k → b ∈ bondsLam P.G j → ∀ v, T.QC j v b = T'.QC j v b ∧ T.DC j v v b = T'.DC j v v b) ∧
  (∀ c : CoarseBond P.Lu P.ell, CRowIn P.ell P.Lam c → ∀ v,
      T.QU v (c.1.1, c.2) = T'.QU v (c.1.1, c.2) ∧ T.DU v v (c.1.1, c.2) = T'.DU v v (c.1.1, c.2))

/-- **READ-SET COMPLETENESS (top level).**  Records agreeing on the top-level read set give the same statement objects. -/
theorem readTop_complete (P : IngrBParams) {T T' : TopJets (scaleUp P.ell P.k P.Lu) P.Lu} (h : AgreeTop P T T') :
    (∀ B, genFormT P T B = genFormT P T' B) ∧ genCT P T = genCT P T' ∧ (WellDefT P T ↔ WellDefT P T') ∧
      (GuardsUnitT P T ↔ GuardsUnitT P T') ∧ (WellDefGT P T ↔ WellDefGT P T') := by
  have hS : sectorT P T = sectorT P T' :=
    sectorJ_congr P.G (fun j b hj hb v => (h.1 j b hj hb v).1) (fun j b hj hb v => (h.1 j b hj hb v).2)
  have hQ := Q1J_rows P.ell P.Lam (T := T.QU) (T' := T'.QU) (fun c hc v => (h.2 c hc v).1)
  have hC := C2tJ_rows P.ell P.Lam (D := T.DU) (D' := T'.DU) (fun c hc v => (h.2 c hc v).2)
  have hW : WellDefT P T ↔ WellDefT P T' := by
    unfold WellDefT; rw [hS]; exact GenS.WellDefS_congr P _ hQ
  have hG : GuardsUnitT P T ↔ GuardsUnitT P T' := by unfold GuardsUnitT; rw [hS]
  refine ⟨fun B => ?_, GenS.genCS_congr P hQ, hW, hG, ?_⟩
  · unfold genFormT; rw [hS]; exact GenS.genFormS_congr P _ hQ hC B
  · unfold WellDefGT; rw [hW, hG]

#print axioms C2fullJ_quad
#print axioms bondSectorOf_eq_J
#print axioms sectorJ_congr
#print axioms Q1jet_eq_J
#print axioms C2tilde_eq_J
#print axioms Q1J_rows
#print axioms C2tJ_rows
#print axioms GenS.genForm_eq_S
#print axioms GenS.genFormS_congr
#print axioms GenS.genCS_congr
#print axioms GenS.WellDefS_congr
#print axioms genForm_eq_T
#print axioms genC_eq_T
#print axioms WellDef_iff_T
#print axioms GuardsUnit_iff_T
#print axioms WellDefG_iff_T
#print axioms readTop_complete

end AdalyFormal.ReadsetComplete
