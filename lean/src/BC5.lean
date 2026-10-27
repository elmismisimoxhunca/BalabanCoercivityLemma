import BC4
import BC1b

/-!
# BC5 -- the full tower: the recursion over `j ≤ k` and the `hm` premise

`TowerClass ell k Lu U ε`: the tower-class link bound `‖Ū^j(b) - 1‖_F ≤ ε_j` on the `ell^j`-aligned bonds of the
blocked backgrounds `Ū^j = bgTower (GF ell k Lu) U j` (`j < k`) -- the `link_tower_na` shape.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

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
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

theorem nrm_zero {L : PeriodicLatticeExtent} (m : ℕ) : nrm m (0 : XS L) = 0 := by
  unfold nrm nr
  have : (fun c : CoarseBond L m => suOf ((0 : XS L) (c.1.1, c.2))) = 0 := by
    funext c
    apply Subtype.ext
    show AdalyFormal.IngredientFamilyR2.toM2 0 = 0
    exact map_zero _
  rw [this]
  simp

section tower
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

abbrev flatBg (ell k : ℕ) (Lu : PeriodicLatticeExtent) : ℕ → PeriodicLinkConfiguration SU2 (scaleUp ell k Lu) :=
  fun _ => trivialU _

theorem regTower_flat (hell : 0 < ell) (J : ℕ) : RegTower ell (flatBg ell k Lu) J := by
  refine regTower_of_small_bc hell (flatBg ell k Lu) J (fun _ => 0) (fun _ => le_rfl)
    (fun j _ e => le_of_eq (frob_trivial_sub_one _ e)) (fun j _ => ?_)
  simp only [mul_zero]
  exact AdalyFormal.NonflatJet.r0_pos

theorem hsLq (hell : 0 < ell) (j : ℕ) (hj : j ≤ k) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = ell ^ j * (scaleUp ell (k - j) Lu μ + 1) := by
  rw [scaleUp_succ ell k Lu hell μ, scaleUp_succ ell (k - j) Lu hell μ]
  have : ell ^ k = ell ^ j * ell ^ (k - j) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

theorem hdvdLq (hell : 0 < ell) (j : ℕ) (hj : j < k) (μ : Fin 3) :
    ell ∣ scaleUp ell (k - j) Lu μ + 1 := by
  rw [scaleUp_succ ell (k - j) Lu hell μ]
  exact Dvd.dvd.mul_left (dvd_pow_self ell (by omega)) _

theorem QlinCompX_zero_apply (ell : ℕ) {L : PeriodicLatticeExtent} (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (a : XS L) : QlinCompX ell bg 0 a = a := by
  simp [QlinCompX, qCompX]

/-- F_j, G_j recursion over the full tower. -/
theorem tower_FG (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (a : XS (scaleUp ell k Lu)) :
    ∀ j, j ≤ k →
      nrm (ell ^ j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a)
        ≤ (rr ell) ^ j * Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) * nrm 1 a
      ∧ nrm (ell ^ j) (QlinCompX ell (bgTower (GF ell k Lu) U) j a - QlinCompX ell (flatBg ell k Lu) j a)
        ≤ (rr ell) ^ j * ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range j, thetaOf ell (ε i)) / rr ell) * nrm 1 a := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  set bg := bgTower (GF ell k Lu) U with hbgdef
  have hstep : ∀ j, j < k →
      nrm (ell ^ (j + 1)) (QlinCompX ell bg (j + 1) a)
          ≤ (rr ell + thetaOf ell (ε j)) * nrm (ell ^ j) (QlinCompX ell bg j a)
      ∧ nrm (ell ^ (j + 1)) (QlinCompX ell bg (j + 1) a - QlinCompX ell (flatBg ell k Lu) (j + 1) a)
          ≤ rr ell * nrm (ell ^ j) (QlinCompX ell bg j a - QlinCompX ell (flatBg ell k Lu) j a)
            + thetaOf ell (ε j) * nrm (ell ^ j) (QlinCompX ell bg j a) := by
    intro j hjk
    have hs := hsLq ell k Lu hell j hjk.le
    have hV : ∀ e : PeriodicLatticeEdge (scaleUp ell (k - j) Lu),
        frobNorm (((resV hs (bg j)) e : M2) - 1) ≤ ε j := by
      intro e
      have hmem : embS hs e.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ j) := by
        rw [mem_CoarseLattice]
        intro μ
        rw [embS_val]
        exact Nat.mul_mod_right _ _
      exact hcl j hjk _ hmem e.2
    have := step_bounds ell bg (flatBg ell k Lu) k hreg (regTower_flat ell k Lu hell k) j hjk hs hell
      (hdvdLq ell k Lu hell j hjk) (ε j) (hε0 j hjk) hV (hsm j hjk) rfl a
    rw [← pow_succ, mul_one] at this
    exact this
  have hX : 0 ≤ nrm 1 a := nrm_nonneg _ _
  have key := seq_bound k (rr ell) hr (fun j => thetaOf ell (ε j))
    (fun j => nrm (ell ^ j) (QlinCompX ell bg j a))
    (fun j => nrm (ell ^ j) (QlinCompX ell bg j a - QlinCompX ell (flatBg ell k Lu) j a)) (nrm 1 a) hX
    (fun j hj => thetaOf_nonneg ell _ (hε0 j hj))
    (by simp [QlinCompX_zero_apply])
    (by simp only [QlinCompX_zero_apply, sub_self, nrm_zero])
    (fun j hj => (hstep j hj).1) (fun j hj => (hstep j hj).2)
  exact key

end tower

#print axioms nrm_zero
#print axioms regTower_flat
#print axioms hsLq
#print axioms hdvdLq
#print axioms QlinCompX_zero_apply
#print axioms tower_FG

end AdalyFormal.BondComposite
