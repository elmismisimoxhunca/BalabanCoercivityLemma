import TL3a

set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section desc
variable {D X Xt Y Yt Z Zt : Type} [Fintype D] [Fintype X] [Fintype Xt] [Fintype Y] [Fintype Yt] [Fintype Z] [Fintype Zt]
  [DecidableEq X] [DecidableEq Xt] [DecidableEq Y] [DecidableEq Yt] [DecidableEq Z] [DecidableEq Zt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (cX : Cov D Xt X) (cY : Cov D Yt Y) (cZ : Cov D Zt Z)

local notation "H" => fun (T : Type) => PiLp 2 (fun _ : T => E)

/-- first intertwining `Õ ℓ = ℓ O` -/
def E1 (O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E))
    (Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)) : Prop :=
  Ot.comp cX.ell = cY.ell.comp O

/-- second intertwining `σ Õ = O σ` -/
def E2 (O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E))
    (Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)) : Prop :=
  cY.sig.comp Ot = O.comp cX.sig

/-- deck equivariance -/
def Equi (Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)) : Prop :=
  ∀ d : D, Ot.comp (cX.pull d) = (cY.pull d).comp Ot

structure Desc (O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E))
    (Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)) : Prop where
  e1 : E1 cX cY O Ot
  e2 : E2 cX cY O Ot
  equi : Equi cX cY Ot

variable {cX cY cZ}

theorem e2_of_e1_equi [Nonempty D] {O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)}
    {Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)}
    (h1 : E1 cX cY O Ot) (he : Equi cX cY Ot) : E2 cX cY O Ot := by
  ext1 f
  apply cY.ell_inj
  have a1 : cY.ell (cY.sig (Ot f)) = ∑ d, cY.pull d (Ot f) := (cY.sum_pull _).symm
  have a2 : ∑ d, cY.pull d (Ot f) = ∑ d, Ot (cX.pull d f) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    exact (congrArg (fun T => T f) (he d)).symm
  have a3 : ∑ d, Ot (cX.pull d f) = Ot (cX.ell (cX.sig f)) := by
    rw [← map_sum, cX.sum_pull]
  have a4 : Ot (cX.ell (cX.sig f)) = cY.ell (O (cX.sig f)) := congrArg (fun T => T (cX.sig f)) h1
  simp only [ContinuousLinearMap.comp_apply]
  rw [a1, a2, a3, a4]

theorem desc_of_e1_equi [Nonempty D] {O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)}
    {Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)}
    (h1 : E1 cX cY O Ot) (he : Equi cX cY Ot) : Desc cX cY O Ot := ⟨h1, e2_of_e1_equi h1 he, he⟩

theorem Desc.comp {O1 : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)}
    {Ot1 : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)}
    {O2 : PiLp 2 (fun _ : Y => E) →L[ℝ] PiLp 2 (fun _ : Z => E)}
    {Ot2 : PiLp 2 (fun _ : Yt => E) →L[ℝ] PiLp 2 (fun _ : Zt => E)}
    (h1 : Desc cX cY O1 Ot1) (h2 : Desc cY cZ O2 Ot2) : Desc cX cZ (O2.comp O1) (Ot2.comp Ot1) := by
  constructor
  · unfold E1
    rw [ContinuousLinearMap.comp_assoc, h1.e1, ← ContinuousLinearMap.comp_assoc, h2.e1, ContinuousLinearMap.comp_assoc]
  · unfold E2
    rw [← ContinuousLinearMap.comp_assoc, h2.e2, ContinuousLinearMap.comp_assoc, h1.e2, ContinuousLinearMap.comp_assoc]
  · intro d
    rw [ContinuousLinearMap.comp_assoc, h1.equi d, ← ContinuousLinearMap.comp_assoc, h2.equi d, ContinuousLinearMap.comp_assoc]

theorem Desc.add {O O' : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)}
    {Ot Ot' : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)}
    (h : Desc cX cY O Ot) (h' : Desc cX cY O' Ot') : Desc cX cY (O + O') (Ot + Ot') := by
  constructor
  · unfold E1; rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, h.e1, h'.e1]
  · unfold E2; rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, h.e2, h'.e2]
  · intro d; rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, h.equi d, h'.equi d]

theorem Desc.smul {O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)}
    {Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)} (r : ℝ)
    (h : Desc cX cY O Ot) : Desc cX cY (r • O) (r • Ot) := by
  constructor
  · unfold E1; rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h.e1]
  · unfold E2; rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, h.e2]
  · intro d; rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h.equi d]

theorem Desc.id : Desc cX cX (ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : X => E))) (ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Xt => E))) :=
  ⟨by unfold E1; simp, by unfold E2; simp, fun d => by simp⟩

theorem Desc.zero : Desc cX cY (0 : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E))
    (0 : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)) :=
  ⟨by unfold E1; simp, by unfold E2; simp, fun d => by simp⟩

theorem Desc.sub {O O' : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)}
    {Ot Ot' : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)}
    (h : Desc cX cY O Ot) (h' : Desc cX cY O' Ot') : Desc cX cY (O - O') (Ot - Ot') := by
  constructor
  · unfold E1; rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, h.e1, h'.e1]
  · unfold E2; rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, h.e2, h'.e2]
  · intro d; rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, h.equi d, h'.equi d]

end desc

end AdalyFormal.Thin
