import RC1

/-!
# RC2 -- the STEP-LEVEL read set: the statement reads the one-step jets only at `ReadRow` rows (each level) and `CRowIn` unit rows

The level composites are the printed chain (3.15) of one-step jets.  `compQ`/`compD` build the chain from ARBITRARY step jets
(`StepJets`); `QlinCompL`/`D2CompL` are `compQ`/`compD` at the r8 steps (`QlinCompL_eq_compQ`, `D2CompL_eq_compD`).

* `comp_congr`: if at every row `(l, e)` that the level-`j` row `b` reads (`ClassJets.ReadRow ell j b l e`) the steps of `J` are
  LOCAL (`StepLocalAt`: row `e` reads its input only on the `ell^l`-aligned sites of the ball `(e₋, 4 ell^(l+1))`) and the steps of
  `J` and `J'` agree as functionals (first order every input, second order on the diagonal), then row `b` of both composites agree.
  Locality is needed for `J` only; no hypothesis on `J'` beyond agreement.
* `r8Steps_local`: the r8 steps are local at every aligned row (from `ClassJets.qStepComp_maskA`, `fderiv_mask`, `fderiv2_mask`),
  with no differentiability hypothesis.
* `readSteps_complete` (**THE READ-SET COMPLETENESS THEOREM**): for every `P` (tower, `Λ`, `U`, `a`: no class, no room, no
  smallness) and every step record `J'` that agrees with the r8 steps on all `ReadRow` rows of all bond-sector rows
  `b ∈ bondsLam j`, `j ≤ k`, and on all `CRowIn` unit rows: `genForm`, `genC`, `WellDef`, `GuardsUnit`, `WellDefG` computed from
  `J'` equal those of the r8 statement.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.ReadsetComplete

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower CRowIn pdist)
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.ClassJets (ReadRow BallA bondsLam_facts scaleUp_dvd qStepComp_maskA)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)

variable {L : PeriodicLatticeExtent}

/-! ## 1. the chain (3.15) from arbitrary step jets -/

noncomputable def compQ (QS : ℕ → (XS L →L[ℝ] XS L)) : ℕ → (XS L →L[ℝ] XS L)
  | 0 => ContinuousLinearMap.id ℝ (XS L)
  | j + 1 => (QS j).comp (compQ QS j)

noncomputable def compD (QS : ℕ → (XS L →L[ℝ] XS L)) (DS : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) :
    ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)
  | 0 => 0
  | j + 1 => LinearMap.mk₂ ℝ
      (fun a b => QS j (compD QS DS j a b) + DS j (compQ QS j a) (compQ QS j b))
      (fun a a' b => by simp only [map_add, LinearMap.add_apply]; abel)
      (fun r a b => by simp only [map_smul, LinearMap.smul_apply, smul_add])
      (fun a b b' => by simp only [map_add, LinearMap.add_apply]; abel)
      (fun r a b => by simp only [map_smul, LinearMap.smul_apply, smul_add])

theorem compQ_succ_apply (QS : ℕ → (XS L →L[ℝ] XS L)) (j : ℕ) (v : XS L) :
    compQ QS (j + 1) v = QS j (compQ QS j v) := rfl

theorem compD_succ_apply (QS : ℕ → (XS L →L[ℝ] XS L)) (DS : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) (j : ℕ) (v w : XS L) :
    compD QS DS (j + 1) v w = QS j (compD QS DS j v w) + DS j (compQ QS j v) (compQ QS j w) := rfl

/-- the r8 composite is the chain of the r8 steps. -/
theorem QlinCompL_eq_compQ (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    ∀ j, QlinCompL ell bg j = compQ (fun l => QlinStepL (ell ^ l) ell (bg l)) j
  | 0 => rfl
  | j + 1 => by rw [QlinCompL_succ, QlinCompL_eq_compQ ell bg j]; rfl

theorem D2CompL_eq_compD (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) :
    ∀ j, D2CompL ell bg j = compD (fun l => QlinStepL (ell ^ l) ell (bg l)) (fun l => D2StepL (ell ^ l) ell (bg l)) j
  | 0 => rfl
  | j + 1 => by
      refine LinearMap.ext (fun a => LinearMap.ext (fun b => ?_))
      show QlinStepL (ell ^ j) ell (bg j) (D2CompL ell bg j a b)
          + D2StepL (ell ^ j) ell (bg j) (QlinCompL ell bg j a) (QlinCompL ell bg j b) = _
      rw [D2CompL_eq_compD ell bg j, QlinCompL_eq_compQ ell bg j]
      rfl

/-! ## 2. locality and the chain congruence -/

/-- row `e` of step `l` reads its input only on the `ell^l`-aligned sites of the ball `(e₋, 4 ell^l ell)`. -/
def StepLocalAt (ell : ℕ) (QS : ℕ → (XS L →L[ℝ] XS L)) (DS : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L))
    (l : ℕ) (e : PeriodicLatticeEdge L) : Prop :=
  (∀ x, QS l x e = QS l (maskX (BallA e.1 (4 * (ell ^ l * ell)) (ell ^ l)) x) e) ∧
  (∀ x, DS l x x e = DS l (maskX (BallA e.1 (4 * (ell ^ l * ell)) (ell ^ l)) x)
      (maskX (BallA e.1 (4 * (ell ^ l * ell)) (ell ^ l)) x) e)

/-- **the r8 steps are local at every aligned row** (no differentiability needed). -/
theorem r8Steps_local (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (l : ℕ)
    (hd : ∀ ρ : Fin 3, ell ^ l ∣ L ρ + 1) (e : PeriodicLatticeEdge L) (he : e.1 ∈ CoarseLattice L (ell ^ l)) :
    StepLocalAt ell (fun l => QlinStepL (ell ^ l) ell (bg l)) (fun l => D2StepL (ell ^ l) ell (bg l)) l e := by
  have hgm := qStepComp_maskA (ell ^ l) ell (pow_pos hell l) hd (bg l) e he
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show QlinStepL (ell ^ l) ell (bg l) x e = QlinStepL (ell ^ l) ell (bg l) (maskX _ x) e
    rw [QlinStepL_apply, QlinStepL_apply]
    exact fderiv_mask _ _ hgm x
  · show D2StepL (ell ^ l) ell (bg l) x x e = D2StepL (ell ^ l) ell (bg l) (maskX _ x) (maskX _ x) e
    rw [D2StepL_apply, D2StepL_apply]
    exact fderiv2_mask _ (maskX_idem _) _ hgm x x

/-- **CHAIN CONGRUENCE.**  Row `b` (aligned at `ell^j`) of the level-`j` composite reads the steps only at its `ReadRow` rows. -/
theorem comp_congr (ell : ℕ) (QS QS' : ℕ → (XS L →L[ℝ] XS L)) (DS DS' : ℕ → (XS L →ₗ[ℝ] XS L →ₗ[ℝ] XS L)) :
    ∀ j (b : PeriodicLatticeEdge L), b.1 ∈ CoarseLattice L (ell ^ j) →
      (∀ l e, ReadRow ell j b l e → StepLocalAt ell QS DS l e ∧ (∀ x, QS l x e = QS' l x e) ∧
        (∀ x, DS l x x e = DS' l x x e)) →
      ∀ v, compQ QS j v b = compQ QS' j v b ∧ compD QS DS j v v b = compD QS' DS' j v v b := by
  intro j
  induction j with
  | zero => intro b _ _ v; exact ⟨rfl, rfl⟩
  | succ j ih =>
      intro b hb hread v
      set s := ell ^ j with hsdef
      have hbs : b.1 ∈ CoarseLattice L s := by
        rw [mem_CoarseLattice] at hb ⊢
        intro ν
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (Nat.dvd_of_mod_eq_zero (hb ν)))
      set W := BallA b.1 (4 * (s * ell)) s with hW
      -- the outer row
      obtain ⟨⟨hlocQ, hlocD⟩, hagQ, hagD⟩ := hread j b ⟨by omega, hb, by rw [pdist_self]; exact Nat.zero_le _⟩
      -- the inner rows
      have hinner : ∀ e : PeriodicLatticeEdge L, e.1 ∈ W →
          compQ QS j v e = compQ QS' j v e ∧ compD QS DS j v v e = compD QS' DS' j v v e := by
        intro e he
        refine ih e he.2 (fun l e' hr => hread l e' ⟨by have := hr.1; omega, hr.2.1, ?_⟩) v
        have h1 := pdist_triangle b.1 e.1 e'.1
        have h2 := he.1
        have h3 := hr.2.2
        have h4 : rhoT ell (l + 1) ≤ rhoT ell j := rhoT_mono ell (by have := hr.1; omega)
        rw [rhoT_succ]
        have h5 : s * ell = ell ^ j * ell := rfl
        omega
      have hmQ : maskX W (compQ QS j v) = maskX W (compQ QS' j v) :=
        maskX_eq_of_agree W (fun e he => (hinner e he).1)
      have hmD : maskX W (compD QS DS j v v) = maskX W (compD QS' DS' j v v) :=
        maskX_eq_of_agree W (fun e he => (hinner e he).2)
      constructor
      · rw [compQ_succ_apply, compQ_succ_apply, hlocQ, hmQ, ← hlocQ, hagQ]
      · rw [compD_succ_apply, compD_succ_apply]
        simp only [Pi.add_apply]
        rw [hlocQ, hmD, ← hlocQ, hagQ, hlocD, hmQ, ← hlocD, hagD]

/-! ## 3. step records and the completeness theorem -/

structure StepJets (Lf Lu : PeriodicLatticeExtent) where
  QS : ℕ → (XS Lf →L[ℝ] XS Lf)
  DS : ℕ → (XS Lf →ₗ[ℝ] XS Lf →ₗ[ℝ] XS Lf)
  QU : XS Lu →L[ℝ] XS Lu
  DU : XS Lu →ₗ[ℝ] XS Lu →ₗ[ℝ] XS Lu

/-- the top-level record of a step record (chain (3.15)). -/
noncomputable def StepJets.top {Lf Lu : PeriodicLatticeExtent} (J : StepJets Lf Lu) : TopJets Lf Lu :=
  ⟨compQ J.QS, compD J.QS J.DS, J.QU, J.DU⟩

/-- the r8 step record. -/
noncomputable def r8Steps (P : IngrBParams) : StepJets (scaleUp P.ell P.k P.Lu) P.Lu :=
  ⟨fun l => QlinStepL (P.G.ell ^ l) P.G.ell (bgTower P.G P.U l), fun l => D2StepL (P.G.ell ^ l) P.G.ell (bgTower P.G P.U l),
    QlinStepL 1 P.ell P.unitBgU, D2StepL 1 P.ell P.unitBgU⟩

theorem r8Top_eq_steps (P : IngrBParams) : r8Top P = (r8Steps P).top := by
  show TopJets.mk (QlinCompL P.G.ell (bgTower P.G P.U)) (D2CompL P.G.ell (bgTower P.G P.U)) _ _
    = TopJets.mk (compQ _) (compD _ _) _ _
  rw [funext (QlinCompL_eq_compQ P.G.ell (bgTower P.G P.U)), funext (D2CompL_eq_compD P.G.ell (bgTower P.G P.U))]
  rfl

/-- **the step-level read set**: `ReadRow` rows of every bond-sector row `b ∈ bondsLam j`, `j ≤ k`, and the `CRowIn` unit rows. -/
def AgreeSteps (P : IngrBParams) (J J' : StepJets (scaleUp P.ell P.k P.Lu) P.Lu) : Prop :=
  (∀ j b, j ≤ P.G.k → b ∈ bondsLam P.G j → ∀ l e, ReadRow P.G.ell j b l e →
      (∀ x, J.QS l x e = J'.QS l x e) ∧ (∀ x, J.DS l x x e = J'.DS l x x e)) ∧
  (∀ c : CoarseBond P.Lu P.ell, CRowIn P.ell P.Lam c → ∀ v,
      J.QU v (c.1.1, c.2) = J'.QU v (c.1.1, c.2) ∧ J.DU v v (c.1.1, c.2) = J'.DU v v (c.1.1, c.2))

/-- locality of `J` at the step-level read set. -/
def StepsLocal (P : IngrBParams) (J : StepJets (scaleUp P.ell P.k P.Lu) P.Lu) : Prop :=
  ∀ j b, j ≤ P.G.k → b ∈ bondsLam P.G j → ∀ l e, ReadRow P.G.ell j b l e → StepLocalAt P.G.ell J.QS J.DS l e

/-- step-level agreement + locality of one side ⇒ top-level agreement. -/
theorem agreeTop_of_steps (P : IngrBParams) {J J' : StepJets (scaleUp P.ell P.k P.Lu) P.Lu}
    (hloc : StepsLocal P J) (h : AgreeSteps P J J') : AgreeTop P J.top J'.top := by
  refine ⟨fun j b hj hb v => ?_, h.2⟩
  have hd : ∀ ρ : Fin 3, P.ell ^ j ∣ scaleUp P.ell P.k P.Lu ρ + 1 := scaleUp_dvd P.ell P.k P.hell P.Lu hj
  have hal := (bondsLam_facts (ell := P.ell) (k := P.k) (S := P.S) hd hb).1
  exact comp_congr P.G.ell J.QS J'.QS J.DS J'.DS j b hal
    (fun l e hr => ⟨hloc j b hj hb l e hr, (h.1 j b hj hb l e hr).1, (h.1 j b hj hb l e hr).2⟩) v

/-- the r8 steps are local on the whole step-level read set of every `P`. -/
theorem r8Steps_localAll (P : IngrBParams) : StepsLocal P (r8Steps P) := by
  intro j b hj hb l e hr
  have hlk : l ≤ P.k := by have := hr.1; have : j ≤ P.k := hj; omega
  have hd : ∀ ρ : Fin 3, P.ell ^ l ∣ scaleUp P.ell P.k P.Lu ρ + 1 := scaleUp_dvd P.ell P.k P.hell P.Lu hlk
  have he : e.1 ∈ CoarseLattice (scaleUp P.ell P.k P.Lu) (P.ell ^ l) := by
    have h := hr.2.1
    rw [mem_CoarseLattice] at h ⊢
    intro ν
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow P.ell (by omega)) (Nat.dvd_of_mod_eq_zero (h ν)))
  exact r8Steps_local P.ell P.hell (bgTower P.G P.U) l hd e he

/-- **READ-SET COMPLETENESS.**  For every `P` (no class, room or smallness hypothesis) and every step record `J'` agreeing with the
r8 steps on the `ReadRow` rows (each level, of every `b ∈ bondsLam j`, `j ≤ k`) and the `CRowIn` unit rows, every statement object
computed from `J'` is the r8 one. -/
theorem readSteps_complete (P : IngrBParams) {J' : StepJets (scaleUp P.ell P.k P.Lu) P.Lu} (h : AgreeSteps P (r8Steps P) J') :
    (∀ B, GenP.genForm P B = genFormT P J'.top B) ∧ GenP.genC P = genCT P J'.top ∧
      (GenP.WellDef P ↔ WellDefT P J'.top) ∧ (GenP.GuardsUnit P ↔ GuardsUnitT P J'.top) ∧
      (GenP.WellDefG P ↔ WellDefGT P J'.top) := by
  have hA := readTop_complete P (agreeTop_of_steps P (r8Steps_localAll P) h)
  rw [← r8Top_eq_steps] at hA
  exact ⟨fun B => hA.1 B, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2⟩

#print axioms QlinCompL_eq_compQ
#print axioms D2CompL_eq_compD
#print axioms r8Steps_local
#print axioms comp_congr
#print axioms r8Top_eq_steps
#print axioms agreeTop_of_steps
#print axioms r8Steps_localAll
#print axioms readSteps_complete

end AdalyFormal.ReadsetComplete
