import BC5
import BC9
import RC2
import TL0

/-!
# TL1 -- region-restricted tower bound (`tower_FG_loc`) by background cut-off

`bgCut bg W l` keeps the links of `bg l` based at sites of `W l` and sets the others to `1`.  The level-`j` row `b`
of the LOCAL composite `QlinCompL` reads the background at level `l < j` only on `Ball b₋ (rhoT j - rhoT l)`
(`compL_cut`, from RC2 `comp_congr` and ZR8Read `qStepComp_congr_bg`).  Hence the rows of level `j` in a finite set `X`
agree with the rows of the cut tower, and the cut tower satisfies the WHOLE-torus class with the REGIONAL `ε`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.TowerLoc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.ReadsetComplete
open AdalyFormal.BondComposite
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the cut-off background: keep the links based in `W l`, set the rest to `1`. -/
def bgCut (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (W : ℕ → Set (PeriodicLatticeSite L)) :
    ℕ → PeriodicLinkConfiguration SU2 L :=
  fun l e => if e.1 ∈ W l ∧ e.1 ∈ CoarseLattice L (ell ^ l) then bg l e else 1

theorem bgCut_agree (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (W : ℕ → Set (PeriodicLatticeSite L))
    (l : ℕ) : AgreeAt (W l ∩ CoarseLattice L (ell ^ l)) (bg l) (bgCut ell bg W l) := by
  classical
  intro z hz μ
  show bg l (z, μ) = (if z ∈ W l ∧ z ∈ CoarseLattice L (ell ^ l) then bg l (z, μ) else 1)
  rw [if_pos ⟨hz.1, hz.2⟩]

theorem bgCut_frob (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (W : ℕ → Set (PeriodicLatticeSite L))
    (ε : ℕ → ℝ) (l : ℕ) (hε : 0 ≤ ε l)
    (hcl : ∀ z ∈ W l, z ∈ CoarseLattice L (ell ^ l) → ∀ μ : Fin 3, frobNorm (((bg l (z, μ) : SU2) : M2) - 1) ≤ ε l)
    (e : PeriodicLatticeEdge L) : frobNorm (((bgCut ell bg W l e : SU2) : M2) - 1) ≤ ε l := by
  unfold bgCut
  by_cases h : e.1 ∈ W l ∧ e.1 ∈ CoarseLattice L (ell ^ l)
  · rw [if_pos h]; exact hcl e.1 h.1 h.2 e.2
  · rw [if_neg h]
    have : ((1 : SU2) : M2) = 1 := rfl
    rw [this, sub_self]
    exact (AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero).le.trans hε

/-- step agreement at one row. -/
theorem step_cut_agree (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (W : ℕ → Set (PeriodicLatticeSite L)) (l : ℕ) (hd : ∀ ρ : Fin 3, ell ^ l ∣ L ρ + 1)
    (e : PeriodicLatticeEdge L) (hal : e.1 ∈ CoarseLattice L (ell ^ l))
    (h : Ball e.1 (4 * (ell ^ l * ell)) ⊆ W l) :
    (∀ x, QlinStepL (ell ^ l) ell (bg l) x e = QlinStepL (ell ^ l) ell (bgCut ell bg W l) x e) ∧
    (∀ x, D2StepL (ell ^ l) ell (bg l) x x e = D2StepL (ell ^ l) ell (bgCut ell bg W l) x x e) := by
  have hq : qStepComp (ell ^ l) ell (bg l) e = qStepComp (ell ^ l) ell (bgCut ell bg W l) e :=
    qStepComp_congr_bg_al (ell ^ l) ell (pow_pos hell l) hd e hal
      ((bgCut_agree ell bg W l).mono (fun z hz => ⟨h hz.1, hz.2⟩))
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [QlinStepL_apply, QlinStepL_apply, hq]
  · rw [D2StepL_apply, D2StepL_apply, hq]

theorem cone_sub (ell : ℕ) (b e : PeriodicLatticeEdge L) (j l : ℕ) (hlj : l < j)
    (hdist : pdist b.1 e.1 ≤ rhoT ell j - rhoT ell (l + 1)) :
    Ball e.1 (4 * (ell ^ l * ell)) ⊆ Ball b.1 (rhoT ell j - rhoT ell l) := by
  refine Ball_sub (y := b.1) (y' := e.1) hdist ?_
  have h1 : rhoT ell (l + 1) ≤ rhoT ell j := rhoT_mono ell (by omega)
  have h2 := rhoT_succ ell l
  omega

/-- **row of the local composite reads the background only in its cone**. -/
theorem compL_cut (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (W : ℕ → Set (PeriodicLatticeSite L)) (j : ℕ) (hd : ∀ l, l < j → ∀ ρ : Fin 3, ell ^ l ∣ L ρ + 1)
    (b : PeriodicLatticeEdge L) (hb : b.1 ∈ CoarseLattice L (ell ^ j))
    (hW : ∀ l, l < j → Ball b.1 (rhoT ell j - rhoT ell l) ⊆ W l) (v : XS L) :
    QlinCompL ell bg j v b = QlinCompL ell (bgCut ell bg W) j v b := by
  rw [QlinCompL_eq_compQ, QlinCompL_eq_compQ]
  refine (comp_congr ell (fun l => QlinStepL (ell ^ l) ell (bg l)) (fun l => QlinStepL (ell ^ l) ell (bgCut ell bg W l))
    (fun l => D2StepL (ell ^ l) ell (bg l)) (fun l => D2StepL (ell ^ l) ell (bgCut ell bg W l)) j b hb ?_ v).1
  intro l e hr
  obtain ⟨hlj, he, hdist⟩ := hr
  have hal : e.1 ∈ CoarseLattice L (ell ^ l) := by
    rw [mem_CoarseLattice] at he ⊢
    intro ν
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (Nat.dvd_of_mod_eq_zero (he ν)))
  have hsub : Ball e.1 (4 * (ell ^ l * ell)) ⊆ W l :=
    (cone_sub ell b e j l hlj hdist).trans (hW l hlj)
  obtain ⟨h1, h2⟩ := step_cut_agree ell hell bg W l (hd l hlj) e hal hsub
  exact ⟨r8Steps_local ell hell bg l (hd l hlj) e hal, h1, h2⟩

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.bgCut_agree
#print axioms AdalyFormal.TowerLoc.bgCut_frob
#print axioms AdalyFormal.TowerLoc.compL_cut
