import TL9c

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section diag
variable {X : Type} [Fintype X] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- diagonal scaling by a weight function -/
noncomputable def diagOp (w : X → ℝ) : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : X => E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun x => w x • (WithLp.ofLp f) x)
      map_add' := fun f g => by ext x; simp [smul_add]
      map_smul' := fun c f => by
        ext x
        simp only [PiLp.smul_apply, RingHom.id_apply, WithLp.ofLp_toLp]
        exact smul_comm _ _ _ }

theorem diagOp_apply (w : X → ℝ) (f : PiLp 2 (fun _ : X => E)) (x : X) : (diagOp w f) x = w x • f x := rfl

theorem inner_diagOp (w : X → ℝ) (f g : PiLp 2 (fun _ : X => E)) : ⟪f, diagOp w g⟫ = ∑ x, w x * ⟪f x, g x⟫ := by
  simp only [PiLp.inner_apply, diagOp_apply, real_inner_smul_right]

end diag

section diagDesc
variable {D Xt X : Type} [Fintype D] [Fintype Xt] [Fintype X] [DecidableEq X] [DecidableEq Xt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem desc_diagOp [Nonempty D] (c : Cov D Xt X) (w : X → ℝ) :
    Desc c c (diagOp (E := E) w) (diagOp (E := E) (fun x => w (c.π x))) := by
  apply desc_of_e1_equi
  · ext1 f
    refine PiLp.ext (fun x => ?_)
    simp only [ContinuousLinearMap.comp_apply, diagOp_apply]
    rfl
  · intro d
    ext1 f
    refine PiLp.ext (fun x => ?_)
    simp only [ContinuousLinearMap.comp_apply, diagOp_apply]
    show (w (c.π x)) • f (c.τ d x) = (diagOp (fun x => w (c.π x)) f) (c.τ d x)
    rw [diagOp_apply, c.π_τ]

end diagDesc

end AdalyFormal.Thin
