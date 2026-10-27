import TL5
import TL6a
import W6I

/-!
# TL6b -- the regional class follows from `M1Regular` (in its gauge), `k`-free; the `hD` drift and `Q*`-injectivity for M1

`WM j l` = the sites within `rhoT j - rhoT l` of a level-`j` row base (`l < j`); `epsM` (TL6a) is the regional `ε`.
* `cone_in_Om` : with `17 ell ≤ R M` the `14 ell^l`-ball around such a site lies in `Ω_{j-1}` (collar, `Admissible` clause 5).
* `hcl_M1` : `dv(Ū^l(U^g)(z,μ)) ≤ epsM j l` for `z ∈ WM j l` `ell^l`-aligned (TL5 `tower_link_loc`, `j0 = j-1`).
* `drift_F_M1` : `hD` of `qs_injective_of_drift` with `D = 3 δ(S*)²`, `S* = SstarM ell f M α₀`, independent of `k`.
* `qs_injective_M1` : `Q*` injective at `U^g` once `3 δ(S*)² CEp < 1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.TowerLoc

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist bigSide)
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.CurvBlock (dv)

variable {L : PeriodicLatticeExtent}

/-- the region of sites read by the level-`j` rows at scale `l < j` -/
def WM (ell k : ℕ) (S : Tower L) (j l : ℕ) : Set (PeriodicLatticeSite L) :=
  {z | l < j ∧ ∃ r : {b : Bond L // b ∈ bondsLam (geomOf ell k S) j}, pdist r.1.1 z ≤ rhoT ell j - rhoT ell l}

/-- **cone geometry** -/
theorem cone_in_Om {ell M R k : ℕ} {S : Tower L} (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S)
    (hroom : 17 * ell ≤ R * M) {j l : ℕ} (hjk : j ≤ k) {z : PeriodicLatticeSite L} (hz : z ∈ WM ell k S j l)
    (w : PeriodicLatticeSite L) (hw : pdist z w ≤ 14 * ell ^ l) : w ∈ S.Om (j - 1) := by
  obtain ⟨hlj, r, hr⟩ := hz
  by_contra hwn
  -- a point of Ω_j within ell^j of the row base
  have hy : ∃ y, y ∈ S.Om j ∧ pdist r.1.1 y ≤ ell ^ j := by
    have hrb := r.2.1
    rcases hrb with h | h
    · exact ⟨r.1.1, h.2.1, by rw [pdist_self]; exact Nat.zero_le _⟩
    · exact ⟨_, h.2.1, pdist_coarseShift_le r.1.1 (ell ^ j) r.1.2⟩
  obtain ⟨y, hyO, hyd⟩ := hy
  have hj1 : 1 ≤ j := by omega
  have hyO' : y ∈ S.Om (j - 1 + 1) := by rw [Nat.sub_add_cancel hj1]; exact hyO
  have hcol := AdalyFormal.M1.collar hS (j := j - 1) (by omega) hwn hyO'
  have hrho := rhoT_le ell hell2 j
  have hP : 1 ≤ ell ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hQ : ell ^ j = ell * ell ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hl : ell ^ l ≤ ell ^ (j - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2P : 2 * ell ^ (j - 1) ≤ ell ^ j := by
    rw [hQ]; exact Nat.mul_le_mul_right _ hell2
  have hRM : 17 * ell ^ j ≤ R * bigSide M ell (j - 1) := by
    unfold bigSide
    rw [hQ]
    calc 17 * (ell * ell ^ (j - 1)) = (17 * ell) * ell ^ (j - 1) := by ring
      _ ≤ (R * M) * ell ^ (j - 1) := Nat.mul_le_mul_right _ hroom
      _ = R * (M * ell ^ (j - 1)) := by ring
  have t1 := pdist_triangle w r.1.1 y
  have t2 := pdist_triangle r.1.1 z w
  have c1 := pdist_comm w r.1.1
  have c2 : pdist r.1.1 z ≤ rhoT ell j - rhoT ell l := hr
  omega

section assembly
variable {ell M R k f : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ η : ℝ}
  (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R) (hroom : 17 * ell ≤ R * M)
  (hT3 : ∀ μ, 3 ≤ Lu μ + 1) (U : LinkCfg (scaleUp ell k Lu))
  (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
  (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
  (hU : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
  (hB : AdalyFormal.M1.M1Bounds S ell M f k α₀ η A) (hη : 0 < η) (hα0 : 0 ≤ α₀)
  (ha1 : (f : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 1)
  (hsmA : (1 + 3 * Real.pi) * rho1 f M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
  (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 f M α₀)) < r0)

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 in
/-- **the regional class from `M1Regular`** (in its gauge `U^g`): the blocked links over the cone of a level-`j` row are
bounded by `epsM j l` (aligned bonds, `l < j`). -/
theorem hcl_M1 (j : Fin (k + 1)) (l : ℕ) (hlk : l < k) (z : PeriodicLatticeSite (scaleUp ell k Lu))
    (hzW : z ∈ WM ell k S j l) (hzA : z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l)) (μ : Fin 3) :
    frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform g U) l (z, μ) : SU2) : M2) - 1)
      ≤ epsM ell f M α₀ j l := by
  have hell : 0 < ell := by omega
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  have hlj : l < (j : ℕ) := hzW.1
  have hcone := cone_in_Om hell2 hS hroom hjk hzW
  have ha0 : 0 ≤ (f : ℝ) * M * α₀ := by positivity
  have hlnk : l ≤ (j : ℕ) - 1 := by omega
  have h := tower_link_loc hell2 hell S hT3 U g A hU hB hη ha0 ha1 hsm4 ((j : ℕ) - 1) l (by omega) hlnk hlk
    z hzA μ hcone
  unfold epsM rho1
  rw [if_pos hlj]
  exact h

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 hsmA hrr in
/-- **`hD` for the M1 regime, `k`-free**: `D = 3 δ(S*)²`, `S* = SstarM ell f M α₀`. -/
theorem drift_F_M1 (hM : 0 < M) (hR : 8 * ell ≤ R) (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wF p * ‖(bondSectorOf (geomOf ell k S) (periodicGaugeTransform g U)).Qfull x p
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
      ≤ 3 * delStar ell (SstarM ell f M α₀) ^ 2 * ‖x‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hsmall : ∀ j l : ℕ, epsM ell f M α₀ j l ≤ 1 / (1000 * (ell : ℝ) ^ 4) := fun j l =>
    (epsM_le ell f M hell α₀ hα0 j l).trans hsmA
  refine drift_F_loc hell2 hS hM hR (periodicGaugeTransform g U) (fun j l => epsM ell f M α₀ j l)
    (fun j l => WM ell k S j l) (fun j l hlk z hzW hzA μ => hcl_M1 hell2 hS hroom hT3 U g A hU hB hη hα0 ha1 hsm4 j l hlk z hzW hzA μ)
    (fun j l _ => epsM_nonneg ell f M α₀ hα0 j l) (fun j l _ => ?_) (fun j l _ => ?_) (fun j r l hl z hz => ?_)
    (SstarM ell f M α₀) (fun j => sum_theta_epsM ell f M hell2 α₀ hα0 hsmA j) x
  · -- hsm
    have h0 := epsM_nonneg ell f M α₀ hα0 j l
    have h1 := rhoOf_le (ell := ell) _ h0
    have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    have hk : epsM ell f M α₀ j l * (ell : ℝ) ^ 4 ≤ 1 / 1000 := by
      have hpos : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_right (hsmall j l) hpos.le
      calc _ ≤ 1 / (1000 * (ell : ℝ) ^ 4) * (ell : ℝ) ^ 4 := this
        _ = 1 / 1000 := by field_simp
    have h4 : (ell : ℝ) ≤ (ell : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((ell : ℝ) - 1), sq_nonneg ((ell : ℝ) ^ 2 - 1)]
    have h5 : (ell : ℝ) * epsM ell f M α₀ j l ≤ 1 / 1000 := by
      nlinarith [mul_le_mul_of_nonneg_right h4 h0]
    have := Real.pi_gt_three
    nlinarith
  · -- hr
    have h0 := epsM_nonneg ell f M α₀ hα0 j l
    have hle := epsM_le ell f M hell α₀ hα0 j l
    refine lt_of_le_of_lt ?_ hrr
    have hpi := Real.pi_pos
    gcongr
  · exact ⟨hl, r, hz⟩

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 hsmA hrr in
/-- **W6 injectivity of `Q*` at `U^g` in the M1 regime**, drift constant `k`-free. -/
theorem qs_injective_M1 (hM : 0 < M) (hR : 8 * ell ≤ R) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hsmall : 3 * delStar ell (SstarM ell f M α₀) ^ 2 * CEp < 1) :
    Function.Injective (gparams ell k Lu (by omega) S (periodicGaugeTransform g U) a Lam).data.Qs :=
  qs_injective_of_drift (by omega) hell2 hS hM hR (periodicGaugeTransform g U) a Lam
    (3 * delStar ell (SstarM ell f M α₀) ^ 2)
    (fun x => drift_F_M1 hell2 hS hroom hT3 U g A hU hB hη hα0 ha1 hsm4 hsmA hrr hM hR x) hsmall

end assembly

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.cone_in_Om
#print axioms AdalyFormal.TowerLoc.hcl_M1
#print axioms AdalyFormal.TowerLoc.drift_F_M1
#print axioms AdalyFormal.TowerLoc.qs_injective_M1
