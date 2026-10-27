import DK3Corridor
import DK3TowerSmooth

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
noncomputable section
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 20000] AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo
  AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo
namespace HConstruction.DK3.Unit
open HConstruction.Carrier HConstruction.Covariance HConstruction.Predicate
attribute [local irreducible] AdalyFormal.Balaban.AdmissibleSubspace.blockOf
  AdalyFormal.Balaban.AdmissibleSubspace.CoarseLattice
  AdalyFormal.Balaban.QjComposite.stepBlockOf
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_trivialU)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.SuTwoInner
local instance : SeminormedAddCommGroup SuTwo := instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

local instance : NormedAddCommGroup (Fine unitL) :=
  @Pi.normedAddCommGroup _ (fun _ : CoarseBond unitL 1 => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo)
local instance : SeminormedAddCommGroup (Fine unitL) :=
  (inferInstance : NormedAddCommGroup (Fine unitL)).toSeminormedAddCommGroup
local instance : NormedSpace ℝ (Fine unitL) :=
  @Pi.normedSpace ℝ _ _ (fun _ : CoarseBond unitL 1 => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup)
    (fun _ => AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo.toNormedSpace)
local instance : NormedAddCommGroup (CoarseBond unitL (1*2) → SuTwo) :=
  @Pi.normedAddCommGroup _ (fun _ : CoarseBond unitL (1*2) => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo)
local instance : SeminormedAddCommGroup (CoarseBond unitL (1*2) → SuTwo) :=
  (inferInstance : NormedAddCommGroup (CoarseBond unitL (1*2) → SuTwo)).toSeminormedAddCommGroup
local instance : NormedSpace ℝ (CoarseBond unitL (1*2) → SuTwo) :=
  @Pi.normedSpace ℝ _ _ (fun _ : CoarseBond unitL (1*2) => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup)
    (fun _ => AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo.toNormedSpace)

/-- Lossless linear recovery of outputs that already lie in su(2). -/
def recover : M2 →L[ℝ] SuTwo :=
  AdalyFormal.Balaban.CovariantOperators.suTwo.subtype.leftInverse.toContinuousLinearMap

lemma recover_coe (X : SuTwo) : recover (X : M2) = X :=
  LinearMap.leftInverse_apply_of_inj AdalyFormal.Balaban.CovariantOperators.suTwo.ker_subtype X

/-- Twice-blocked background, not a second application of the old unit jet. -/
abbrev unitU := HConstruction.DK3.V

theorem unitU_zero : unitU 0 = trivialU unitL := V_zero

theorem smoothAt_unitU (b : Bond unitL) : ContDiffAt ℝ ⊤ (fun t => (unitU t b : M2)) 0 :=
  smooth_V b

/-- Raw time-one unit average (2 in the input of the eta=1/2 normalized chart),
not the fine variational pullback and not a fixed flat background. -/
def raw (t : ℝ) (B : K) : W :=
  (cfl2Equiv 2).symm (fun c => recover (actualQ (unitU t) 2 (unitInput ((2:ℝ) • B)) c))

theorem smoothAt_raw_joint : ContDiffAt ℝ ⊤ (fun z : ℝ × K => raw z.1 z.2) (0,0) := by
  have hp : ContDiffAt ℝ ⊤ (fun z : ℝ × K => fun c : CoarseBond unitL (1*2) =>
      recover (actualQ (unitU z.1) 2 (unitInput ((2:ℝ) • z.2)) c)) (0,0) := by
    apply contDiffAt_pi.mpr
    intro c
    apply recover.contDiff.contDiffAt.comp
    apply HConstruction.G0CoerceFinal.Joint.family_actualQ_smooth
    · intro e
      have hc := (smoothAt_unitU e).comp (0,0)
        (contDiffAt_fst (𝕜 := ℝ) (n := ⊤) (p := ((0,0) : ℝ × K)))
      dsimp only [Function.comp_def] at hc
      exact hc
    · exact unitInput.contDiff.contDiffAt.comp (0,0) (contDiffAt_snd.const_smul 2)
    · simp
    · intro y hy
      left
      rw [unitU_zero]
      simp [AdalyFormal.Balaban.UbarTowerCov.loopVar,
        AdalyFormal.Balaban.UbarTowerCov.gammaVarStrided,
        AdalyFormal.Balaban.UbarTowerCov.coarseBondVar,
        AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU]
  exact (cfl2Equiv (L := unitL) 2).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp (0,0) hp

/-- Q1's raw normalization is used consistently for both constraint and lift. -/
def rawQ (t : ℝ) : K →L[ℝ] W := fderiv ℝ (raw t) 0

theorem smoothAt_rawQ : ContDiffAt ℝ ⊤ rawQ 0 :=
  smoothAt_raw_joint.fderiv contDiffAt_const (by simp)

def outMatrix (c : CoarseBond unitL (1*2)) : W →L[ℝ] M2 :=
  (AdalyFormal.Balaban.CovariantOperators.suTwo.subtype.comp
    ((LinearMap.proj c).comp (cfl2Equiv 2).toLinearMap)).toContinuousLinearMap

open AdalyFormal.Balaban.SuTwoLogExp (coe_mul coe_inv su2NegOne su2NegOne_ne_one)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy_trivialU)

private theorem smoothAt_mul {V W : ℝ → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => (V t : M2)) 0)
    (hW : ContDiffAt ℝ ⊤ (fun t => (W t : M2)) 0) :
    ContDiffAt ℝ ⊤ (fun t => ((V t * W t : SU2) : M2)) 0 := by
  simpa only [coe_mul] using hV.mul hW

private theorem smoothAt_inv {V : ℝ → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => (V t : M2)) 0) :
    ContDiffAt ℝ ⊤ (fun t => (((V t)⁻¹ : SU2) : M2)) 0 := by
  have h := AdalySI1.L7.conjTransposeCLM.contDiff.contDiffAt.comp 0 hV
  change ContDiffAt ℝ ⊤ (fun t => (V t : M2).conjTranspose) 0 at h
  simpa only [coe_inv] using h

theorem smoothAt_unit_loop (c : CoarseBond unitL (1*2)) (x : PeriodicLatticeSite unitL) :
    ContDiffAt ℝ ⊤ (fun t => ((loopVar 1 2 (unitU t) (c.1.1,c.2) x : SU2) : M2)) 0 := by
  unfold loopVar gammaVarStrided coarseBondVar
  exact smoothAt_mul (smoothAt_mul (smoothAt_mul
    (HConstruction.SmallNFSmooth.smooth_coarsePath smoothAt_unitU _ _ _)
    (HConstruction.SmallNFSmooth.smooth_coarsePath smoothAt_unitU _ _ _))
    (smoothAt_inv (HConstruction.SmallNFSmooth.smooth_coarsePath smoothAt_unitU _ _ _)))
    (smoothAt_inv (HConstruction.SmallNFSmooth.smooth_coarsePath smoothAt_unitU _ _ _))

theorem eventually_unit_loop_uncut : ∀ᶠ t in nhds (0:ℝ),
    ∀ c : CoarseBond unitL (1*2), ∀ x : PeriodicLatticeSite unitL,
      loopVar 1 2 (unitU t) (c.1.1,c.2) x ≠ su2NegOne := by
  apply Filter.eventually_all.mpr
  intro c
  apply Filter.eventually_all.mpr
  intro x
  have h0 : loopVar 1 2 (unitU 0) (c.1.1,c.2) x = 1 := by
    rw [unitU_zero]
    simp [loopVar, gammaVarStrided, coarseBondVar, coarsePathHolonomy_trivialU]
  have hne : ((loopVar 1 2 (unitU 0) (c.1.1,c.2) x : SU2) : M2) ≠ (su2NegOne : M2) := by
    rw [h0]
    exact fun h => su2NegOne_ne_one (Subtype.ext h.symm)
  have he := (smoothAt_unit_loop c x).continuousAt.eventually_ne hne
  filter_upwards [he] with t ht
  exact fun h => ht (congrArg Subtype.val h)

/-- Literal q124 on the induced unit background, in RAW input normalization. -/
abbrev nativeRawQ := HConstruction.DK3.nativeRawQ

attribute [local irreducible] AdalyFormal.DeltaKR85.q124Principal

theorem nativeRawQ_exact (t : ℝ) (B : K) (c : CoarseBond unitL (1*2)) :
    outMatrix c (nativeRawQ t B) = linearQ (unitU t) 2 ((2:ℝ) • unitInput B) c := rfl

theorem raw_exact (t : ℝ) (B : K) (c : CoarseBond unitL (1*2)) :
    outMatrix c (raw t B) = actualQ (unitU t) 2 ((2:ℝ) • unitInput B) c := by
  have h := recover_coe (⟨actualQ (unitU t) 2 (unitInput ((2:ℝ) • B)) c, actualQ_mem _ _ _ _⟩ : SuTwo)
  have hc := congrArg (fun X : SuTwo => (X : M2)) h
  change (recover (actualQ (unitU t) 2 (unitInput ((2:ℝ) • B)) c) : M2) = _
  simpa only [map_smul] using hc

theorem rawQ_eq_native (t : ℝ) (hs : DifferentiableAt ℝ (raw t) 0)
    (hg : ∀ c : CoarseBond unitL (1*2), ∀ x : PeriodicLatticeSite unitL,
      loopVar 1 2 (unitU t) (c.1.1,c.2) x ≠ su2NegOne) : rawQ t = nativeRawQ t := by
  apply ContinuousLinearMap.ext
  intro B
  apply (cfl2Equiv 2).injective
  funext c
  apply Subtype.ext
  have hd := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ)
    ((hasDerivAt_id 0).smul_const B) (by simp)
  have hm := (outMatrix c).hasFDerivAt.comp_hasDerivAt (0:ℝ) hd
  have hjet := actualQ_firstJet (unitU t) 2 (by decide) unit_even (fun c x _ => hg c x)
    ((2:ℝ) • unitInput B) c
  have heq : (fun s : ℝ => outMatrix c (raw t (s • B))) =
      (fun s : ℝ => actualQ (unitU t) 2 (s • ((2:ℝ) • unitInput B)) c) := by
    funext s
    rw [raw_exact, map_smul, smul_comm (2:ℝ)]
  simp only [Function.comp_def, id_eq, one_smul] at hm
  change HasDerivAt (fun s : ℝ => outMatrix c (raw t (s • B)))
    (outMatrix c (rawQ t B)) 0 at hm
  rw [heq] at hm
  exact hm.unique hjet

theorem rawQ_zero : rawQ 0 = rawLinear := by
  have hs : ContDiffAt ℝ ⊤ (raw 0) 0 :=
    smoothAt_raw_joint.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  rw [rawQ_eq_native 0 (hs.differentiableAt (by simp)) (by
    intro c x
    rw [unitU_zero]
    exact trivial_loop_guard 2 c x)]
  rfl

theorem eventually_raw_smooth : ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ 2 (raw t) 0 := by
  have hev : ∀ᶠ z in nhds ((0,0) : ℝ × K), ContDiffAt ℝ 2 (fun z : ℝ × K => raw z.1 z.2) z :=
    (smoothAt_raw_joint.of_le (by simp)).eventually (by simp)
  have hl : Filter.Tendsto (fun t : ℝ => (t,(0:K))) (nhds 0) (nhds ((0,0) : ℝ × K)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [hl.eventually hev] with t ht
  exact ht.comp 0 (contDiffAt_const.prodMk contDiffAt_id)

theorem eventually_rawQ_native : ∀ᶠ t in nhds (0:ℝ), rawQ t = nativeRawQ t := by
  filter_upwards [eventually_unit_loop_uncut, eventually_raw_smooth] with t hg hs
  exact rawQ_eq_native t (hs.differentiableAt (by norm_num)) hg

end HConstruction.DK3.Unit
