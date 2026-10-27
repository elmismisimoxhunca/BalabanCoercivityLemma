import SG8

/-!
# SG9 -- locality and gauge covariance of the rows of `Q_U` (lane m2_fields123_20261015)

* `Qfull_row_congr` : the row `p` (level `j`, bond `b`) of `Q_U` depends on `U` only through `bgTower U l` on `Ball b.1 (ρ_j − ρ_l)`, `l < j` (`compL_cut`);
  in particular on `AgreeAt (Ball b.1 (rhoT ell j))`; for `j = 0` it does not depend on `U` at all.
* `RowQ_gauge` : `RowQ (U^γ) p ⇒ RowQ U p` (`QfullOf_gauge`: `Q_{U^γ} Ad_γ = Ad_γ Q_U` row by row).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2F123

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.DLayer (Foot bondRestr)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.BondComposite
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT rhoT_mono Ball_sub bgTower_congr)
open AdalyFormal.W6
open AdalyFormal.NonflatJet
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc
open AdalyFormal.GaugeCov (adBL adFL QfullOf_gauge adFL_apply)

variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem Qfull_row_congr (hell : 0 < ell) (V V' : Cfg (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S))
    (h : ∀ l, l < (p.1 : ℕ) → ∀ z : PeriodicLatticeSite (scaleUp ell k Lu),
      pdist p.2.1.1 z ≤ rhoT ell p.1 - rhoT ell l → ∀ μ : Fin 3,
      bgTower (GF ell k Lu) V l (z, μ) = bgTower (GF ell k Lu) V' l (z, μ))
    (y : BondFnL2 (scaleUp ell k Lu)) :
    (bondSectorOf (geomOf ell k S) V).Qfull y p = (bondSectorOf (geomOf ell k S) V').Qfull y p := by
  classical
  have hjk : (p.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have hal := row_aligned (S := S) hell p
  have hd : ∀ l, l < (p.1 : ℕ) → ∀ ρ : Fin 3, ell ^ l ∣ scaleUp ell k Lu ρ + 1 :=
    fun l hl ρ => hdvd_scaleUp ell k Lu hell l (by omega) ρ
  set j : ℕ := (p.1 : ℕ) with hj
  set b := p.2.1 with hb
  let W : ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)) := fun l => {z | l < j ∧ pdist b.1 z ≤ rhoT ell j - rhoT ell l}
  have hW : ∀ l, l < j → Ball b.1 (rhoT ell j - rhoT ell l) ⊆ W l := fun l hl z hz => ⟨hl, hz⟩
  have hcut : bgCut ell (bgTower (GF ell k Lu) V) W = bgCut ell (bgTower (GF ell k Lu) V') W := by
    funext l e
    unfold bgCut
    by_cases h1 : e.1 ∈ W l ∧ e.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l)
    · rw [if_pos h1, if_pos h1]
      exact h l h1.1.1 e.1 h1.1.2 e.2
    · rw [if_neg h1, if_neg h1]
  have e1 : ∀ (U : Cfg (scaleUp ell k Lu)) (z : BondFnL2 (scaleUp ell k Lu)), (bondSectorOf (geomOf ell k S) U).Qfull z p
      = (((ell : ℝ) ^ j)⁻¹) • suOf (QlinCompL ell (bgTower (GF ell k Lu) U) p.1 (suCoord z) p.2.1) := fun U z => rfl
  rw [e1, e1, compL_cut ell hell (bgTower (GF ell k Lu) V) W j hd b hal hW,
    compL_cut ell hell (bgTower (GF ell k Lu) V') W j hd b hal hW, hcut]

theorem Qfull_row_congr_agree (hell : 0 < ell) (V V' : Cfg (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S))
    (h : AgreeAt (Ball p.2.1.1 (rhoT ell p.1)) V V') (y : BondFnL2 (scaleUp ell k Lu)) :
    (bondSectorOf (geomOf ell k S) V).Qfull y p = (bondSectorOf (geomOf ell k S) V').Qfull y p := by
  refine Qfull_row_congr hell V V' p ?_ y
  intro l hl z hz μ
  refine bgTower_congr (GF ell k Lu) hell l z ?_ μ
  refine h.mono ?_
  have e : rhoT (GF ell k Lu).ell l = rhoT ell l := rfl
  refine Ball_sub (y := p.2.1.1) (y' := z) hz ?_
  rw [e]
  have := rhoT_mono ell (le_of_lt hl)
  omega

theorem RowQ_transfer (hell : 0 < ell) {V V' : Cfg (scaleUp ell k Lu)} {Sstar : ℝ} (p : BIdx (geomOf ell k S))
    (h : ∀ y : BondFnL2 (scaleUp ell k Lu),
      (bondSectorOf (geomOf ell k S) V).Qfull y p = (bondSectorOf (geomOf ell k S) V').Qfull y p)
    (hV : RowQ ell k Lu S V' Sstar p) : RowQ ell k Lu S V Sstar p := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rw [h y, h (bondRestr (Foot ell (p.1 : ℕ) p.2.1) y)]; exact hV.1 y
  · rw [h y]; exact hV.2 y

theorem bondRestr_adBL (γ : GaugeFn (scaleUp ell k Lu)) (F : PeriodicLatticeEdge (scaleUp ell k Lu) → Prop) [DecidablePred F]
    (y : BondFnL2 (scaleUp ell k Lu)) : adBL γ (bondRestr F y) = bondRestr F (adBL γ y) := by
  refine PiLp.ext (fun b => ?_)
  show RMap (γ b.1) ((bondRestr F y).ofLp b) = (bondRestr F (adBL γ y)).ofLp b
  simp only [bondRestr, WithLp.ofLp_toLp]
  by_cases hF : F b
  · simp only [if_pos hF]; rfl
  · simp only [if_neg hF, map_zero]

theorem RMap_inj (g : ↥AdalyFormal.Balaban.AlphaAnalyticity.SU2) {x y : ↥SuTwo} (h : RMap g x = RMap g y) : x = y := by
  have h1 : RMap g (x - y) = 0 := by rw [map_sub, h, sub_self]
  have h2 : ‖x - y‖ = 0 := by
    rw [← AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap g (x - y), h1, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

theorem RowQ_gauge (γ : GaugeFn (scaleUp ell k Lu)) (U : Cfg (scaleUp ell k Lu)) {Sstar : ℝ} (p : BIdx (geomOf ell k S))
    (h : RowQ ell k Lu S (periodicGaugeTransform γ U) Sstar p) : RowQ ell k Lu S U Sstar p := by
  classical
  have hrow : ∀ y : BondFnL2 (scaleUp ell k Lu),
      (bondSectorOf (geomOf ell k S) (periodicGaugeTransform γ U)).Qfull (adBL γ y) p
        = RMap (γ p.2.1.1) ((bondSectorOf (geomOf ell k S) U).Qfull y p) := by
    intro y
    have := congrArg (fun f => f.ofLp p) (QfullOf_gauge (geomOf ell k S) U γ y)
    rw [adFL_apply] at this
    exact this
  refine ⟨fun y => ?_, fun y => ?_⟩
  · have h1 := h.1 (adBL γ y)
    rw [hrow y, ← bondRestr_adBL, hrow] at h1
    exact RMap_inj _ h1
  · have h1 := h.2 (adBL γ y)
    rw [hrow y, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, LinearIsometryEquiv.norm_map] at h1
    exact h1

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.Qfull_row_congr
#print axioms AdalyFormal.M2F123.Qfull_row_congr_agree
#print axioms AdalyFormal.M2F123.RowQ_transfer
#print axioms AdalyFormal.M2F123.bondRestr_adBL
#print axioms AdalyFormal.M2F123.RowQ_gauge
