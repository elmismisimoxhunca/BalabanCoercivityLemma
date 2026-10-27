import ZGU1A
import AdalyFormal.Balaban.TowerLawCovariant
import AdalyFormal.Balaban.FourierFaithfulU1

/-!
# GU1B -- the flat multi-level jet `QlinCompX ell flat j` is `ell^j * (the ell^j-block line average)`
(the "flat multi-level Q_j closed form", r2 residual R4), for ALL j, by induction using
`QlinCompX_succ`, `Dtot_flat_eq_s` (GU1A) and the tree's `tower_law`.
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.GenuineU1

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice mem_CoarseLattice mem_blockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero)
open AdalyFormal.Balaban.ThirdLevelArrows (unitToCoarse unitSitesOf unitToCoarse_smul pathSite_mul_coarse tower_law)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo lineCoarseRestrictCovLM
  lineCoarseRestrictCov_trivialU)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

variable {L : PeriodicLatticeExtent}

theorem sum_unitSites {M : Type*} [AddCommMonoid M] (n ell : ℕ) {y : PeriodicLatticeSite L}
    (hys : y ∈ CoarseLattice L n) (g : PeriodicLatticeSite L → M) :
    ∑ u ∈ unitSitesOf n (n * ell) y, g u.1 = ∑ x ∈ stepBlockOf y n ell, g x := by
  classical
  rw [stepBlock_eq_filter hys]
  unfold unitSitesOf
  rw [Finset.sum_filter]
  have h := Finset.sum_coe_sort (CoarseLattice L n)
    (fun z => if z ∈ blockOf y (n * ell) then g z else 0)
  have h2 : (∑ a : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L n},
      if a.1 ∈ blockOf y (n * ell) then g a.1 else 0) =
      ∑ i ∈ CoarseLattice L n, if i ∈ blockOf y (n * ell) then g i else 0 := by
    convert h using 1
    congr!
  rw [h2]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_filter]
  tauto

/-- one flat step in closed form, in the su(2)-valued carrier: `Q_step = ell • unitToCoarse` -/
theorem step_closed (n ell : ℕ) (hn : 0 < n) (hell : 0 < ell) (hdvd : ∀ ν, n * ell ∣ (L ν + 1))
    (a : XS L) (c : CoarseBond L (n * ell)) :
    suCoordFInv (QlinStepX n ell flatCfg a) (c.1.1, c.2)
      = (ell : ℝ) • unitToCoarse n ell (fun d : CoarseBond L n => suCoordFInv a (d.1.1, d.2)) c := by
  have hdn : ∀ ν, n ∣ L ν + 1 := fun ν => dvd_trans (dvd_mul_right n ell) (hdvd ν)
  have hc : c.1.1 ∈ CoarseLattice L (n * ell) := c.1.2
  have hcn : c.1.1 ∈ CoarseLattice L n := by
    rw [mem_CoarseLattice] at hc ⊢
    intro ν
    exact Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_right n ell) (Nat.dvd_of_mod_eq_zero (hc ν)))
  set e : PeriodicLatticeEdge L := (c.1.1, c.2) with he
  have hD := Dtot_flat_eq_s n ell hn hell hdvd e hc
  -- LHS as a double sum
  have hL : suCoordFInv (QlinStepX n ell flatCfg a) e
      = ∑ x ∈ stepBlockOf c.1.1 n ell, (((ell : ℝ) ^ 3)⁻¹) •
          ∑ i ∈ Finset.range ell, suCoordFInv a (pathSite x c.2 (i * n), c.2) := by
    apply Subtype.ext
    show toM2 (QlinStepX n ell flatCfg a e) = _
    rw [QlinStepX_flat_apply, hD]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, bondL_apply]
    rw [show (∑ x ∈ stepBlockOf e.1 n ell, Wt ell • ∑ i ∈ Finset.range ell, toM2 (a (pathSite x e.2 (i * n), e.2)))
        = toM2 (∑ x ∈ stepBlockOf e.1 n ell, Wt ell • ∑ i ∈ Finset.range ell, a (pathSite x e.2 (i * n), e.2)) by
          simp [map_sum, map_smul], fromM2_toM2]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
    rfl
  rw [hL]
  unfold unitToCoarse
  have hinner : ∀ u : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L n},
      (∑ i ∈ Finset.range ell,
        (if h : pathSite u.1 c.2 (i * n) ∈ CoarseLattice L n then
          (fun d : CoarseBond L n => suCoordFInv a (d.1.1, d.2))
            (⟨⟨pathSite u.1 c.2 (i * n), h⟩, c.2⟩ : CoarseBond L n)
         else 0))
      = ∑ i ∈ Finset.range ell, suCoordFInv a (pathSite u.1 c.2 (i * n), c.2) := by
    intro u
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dif_pos (pathSite_mul_coarse n hdn u.2 c.2 i)]
  rw [Finset.sum_congr rfl (fun u _ => hinner u)]
  rw [sum_unitSites n ell hcn (fun x => ∑ i ∈ Finset.range ell, suCoordFInv a (pathSite x c.2 (i * n), c.2))]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  have : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  field_simp

open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCovLM_apply) in
/-- **FLAT MULTI-LEVEL Q_j CLOSED FORM.**  At the flat tower, for every level `j ≤ J` on a torus with
`ell^J ∣ L+1`: `L^j Q_j` (the jet `QlinCompX ell bg j`) read at a stride-`n=ell^j` coarse bond is
`n` times the `n`-block line average `lineCoarseRestrictSuTwo n`. -/
theorem Qcomp_closed (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (hbg : ∀ j, bg j = flatCfg) (J : ℕ) (hdvdJ : ∀ ν, ell ^ J ∣ L ν + 1) (a : XS L) :
    ∀ j, j ≤ J → ∀ (n : ℕ), n = ell ^ j → ∀ c : CoarseBond L n,
      suCoordFInv (QlinCompX ell bg j a) (c.1.1, c.2)
        = (n : ℝ) • lineCoarseRestrictSuTwo n (suCoordFInv a) c := by
  have hreg : RegTower ell bg J := fun j _ => by rw [hbg j]; exact RegBg_flat _ _
  intro j
  induction j with
  | zero =>
      intro _ n hn c
      have hn1 : n = 1 := by simpa using hn
      subst hn1
      have hid : QlinCompX ell bg 0 = ContinuousLinearMap.id ℝ (XS L) := by
        unfold QlinCompX
        exact fderiv_id
      rw [hid]
      simp only [ContinuousLinearMap.id_apply, Nat.cast_one, one_smul]
      unfold lineCoarseRestrictSuTwo
      rw [AdalyFormal.Balaban.FourierFaithfulU1.blockOf_one]
      simp [pathSite_zero]
  | succ j ih =>
      intro hj n' hn' c
      have hn'' : n' = ell ^ j * ell := by rw [hn', pow_succ]
      subst hn''
      have hell1 : 0 < ell ^ j := pow_pos hell j
      have hdvd1 : ∀ ν, ell ^ j * ell ∣ L ν + 1 := fun ν =>
        dvd_trans (by rw [← pow_succ]; exact pow_dvd_pow ell hj) (hdvdJ ν)
      have hdn : ∀ ν, ell ^ j ∣ L ν + 1 := fun ν => dvd_trans (dvd_mul_right _ _) (hdvd1 ν)
      have hchain := QlinCompX_succ ell bg J hreg j (by omega)
      have hih := ih (by omega) (ell ^ j) rfl
      rw [hchain, ContinuousLinearMap.comp_apply, hbg j]
      rw [step_closed (ell ^ j) ell hell1 hell hdvd1 _ c]
      have hfun : (fun d : CoarseBond L (ell ^ j) => suCoordFInv (QlinCompX ell bg j a) (d.1.1, d.2))
          = ((ell ^ j : ℕ) : ℝ) • (fun d : CoarseBond L (ell ^ j) => lineCoarseRestrictSuTwo (ell ^ j) (suCoordFInv a) d) := by
        funext d; exact hih d
      rw [hfun, unitToCoarse_smul]
      have htl := congrFun (tower_law (L := L) hell1 hell hdn (suCoordFInv a)) c
      rw [show (lineCoarseRestrictCovLM (trivialU L) (ell ^ j) (suCoordFInv a))
          = fun d => lineCoarseRestrictSuTwo (ell ^ j) (suCoordFInv a) d from
          funext fun d => lineCoarseRestrictCov_trivialU _ _ d] at htl
      rw [lineCoarseRestrictCovLM_apply, lineCoarseRestrictCov_trivialU] at htl
      rw [htl, smul_smul]
      push_cast
      ring_nf

#print axioms Qcomp_closed

end AdalyFormal.GenuineU1
