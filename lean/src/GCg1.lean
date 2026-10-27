import R2Algebra

/-!
# GCg1 -- generic equivariance of the R2Algebra layer (`BaseDataS`, `Ginv`, `G`, `H`, `K`,
`IsG1inv`, `G1`, `H1`) under linear isometric equivalences `AE`, `AS`, `AF` of `E`, `S`, `F`.

`Ring.inverse` is handled in BOTH cases (unit / non-unit): conjugation by a continuous linear
equivalence is a multiplicative equivalence of `X →L X`, so it preserves `IsUnit` and commutes with
`Ring.inverse` (both sides `0` in the non-unit case).
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2

/-- conjugation commutes with `Ring.inverse` (unit and non-unit case). -/
theorem conj_ringInverse {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (e : X ≃L[ℝ] X) (M : X →L[ℝ] X) :
    Ring.inverse (e.conjContinuousAlgEquiv M) = e.conjContinuousAlgEquiv (Ring.inverse M) := by
  set φ := e.conjContinuousAlgEquiv with hφ
  by_cases hu : IsUnit M
  · have hab : φ M * φ (Ring.inverse M) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel M hu, map_one]
    have hba : φ (Ring.inverse M) * φ M = 1 := by
      rw [← map_mul, Ring.inverse_mul_cancel M hu, map_one]
    have hU : IsUnit (φ M) := ⟨⟨φ M, φ (Ring.inverse M), hab, hba⟩, rfl⟩
    calc Ring.inverse (φ M) = Ring.inverse (φ M) * (φ M * φ (Ring.inverse M)) := by rw [hab, mul_one]
      _ = (Ring.inverse (φ M) * φ M) * φ (Ring.inverse M) := by rw [mul_assoc]
      _ = φ (Ring.inverse M) := by rw [Ring.inverse_mul_cancel _ hU, one_mul]
  · have hu' : ¬ IsUnit (φ M) := by
      intro h
      apply hu
      have h2 := h.map (φ.symm : (X →L[ℝ] X) →* (X →L[ℝ] X))
      simpa using h2
    rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ hu', map_zero]

/-- intertwined operators have intertwined `Ring.inverse`s. -/
theorem ringInverse_intertwine {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (e : X ≃L[ℝ] X) {M M' : X →L[ℝ] X} (h : ∀ x, M' (e x) = e (M x)) (x : X) :
    Ring.inverse M' (e x) = e (Ring.inverse M x) := by
  have hM : M' = e.conjContinuousAlgEquiv M := by
    ext y
    rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    have := h (e.symm y)
    rwa [e.apply_symm_apply] at this
  rw [hM, conj_ringInverse, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    e.symm_apply_apply]

variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The six commuting hypotheses of task G1 (`D'` is the transform of `D`). -/
structure BaseEqv (AE : E ≃ₗᵢ[ℝ] E) (AS : S ≃ₗᵢ[ℝ] S) (AF : F ≃ₗᵢ[ℝ] F)
    (D D' : BaseDataS E S F) : Prop where
  Dpi : ∀ x, D'.Dpi (AE x) = AE (D.Dpi x)
  T : ∀ x, D'.T (AE x) = AS (D.T x)
  Q : ∀ x, D'.Q (AE x) = AF (D.Q x)
  Mass : ∀ x, D'.Mass (AE x) = AE (D.Mass x)
  C2 : ∀ x, D'.C2 (AE x) = AF (D.C2 x)
  J : D'.J = AE D.J

namespace BaseEqv
variable {AE : E ≃ₗᵢ[ℝ] E} {AS : S ≃ₗᵢ[ℝ] S} {AF : F ≃ₗᵢ[ℝ] F} {D D' : BaseDataS E S F}

theorem Ts (h : BaseEqv AE AS AF D D') (s : S) : D'.Ts (AS s) = AE (D.Ts s) := by
  apply ext_inner_left ℝ
  intro v
  obtain ⟨y, rfl⟩ := AE.surjective v
  rw [← D'.T_adj, h.T, AS.inner_map_map, AE.inner_map_map, D.T_adj]

theorem Qs (h : BaseEqv AE AS AF D D') (f : F) : D'.Qs (AF f) = AE (D.Qs f) := by
  apply ext_inner_left ℝ
  intro v
  obtain ⟨y, rfl⟩ := AE.surjective v
  rw [← D'.Q_adj, h.Q, AF.inner_map_map, AE.inner_map_map, D.Q_adj]

theorem Ginv (h : BaseEqv AE AS AF D D') (x : E) : D'.Ginv (AE x) = AE (D.Ginv x) := by
  simp only [BaseDataS.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    h.Dpi, h.T, h.Ts, h.Mass, map_add]

theorem G (h : BaseEqv AE AS AF D D') (x : E) : D'.G (AE x) = AE (D.G x) :=
  ringInverse_intertwine AE.toContinuousLinearEquiv (fun y => h.Ginv y) x

/-- generic `H`-type operator `P Qs (Q P Qs)⁻¹` for an intertwined `P`. -/
theorem Hgen (h : BaseEqv AE AS AF D D') {P P' : E →L[ℝ] E} (hP : ∀ x, P' (AE x) = AE (P x))
    (f : F) :
    ((P'.comp D'.Qs).comp (Ring.inverse ((D'.Q.comp P').comp D'.Qs))) (AF f) =
      AE (((P.comp D.Qs).comp (Ring.inverse ((D.Q.comp P).comp D.Qs))) f) := by
  have hR := ringInverse_intertwine AF.toContinuousLinearEquiv
    (M := (D.Q.comp P).comp D.Qs) (M' := (D'.Q.comp P').comp D'.Qs)
    (fun y => by
      simp only [ContinuousLinearMap.comp_apply]
      exact (by rw [show (AF.toContinuousLinearEquiv : F → F) y = AF y from rfl, h.Qs, hP, h.Q]; rfl))
    f
  simp only [ContinuousLinearMap.comp_apply]
  rw [show AF f = (AF.toContinuousLinearEquiv : F → F) f from rfl, hR]
  exact (by rw [show (AF.toContinuousLinearEquiv : F → F) _ = AF _ from rfl, h.Qs, hP])

theorem H (h : BaseEqv AE AS AF D D') (f : F) : D'.H (AF f) = AE (D.H f) :=
  h.Hgen (fun x => h.G x) f

theorem K (h : BaseEqv AE AS AF D D') (A : E) : D'.K (AE A) = D.K A := by
  simp only [BaseDataS.K, h.Dpi, h.C2, h.H, h.J, h.T, h.Mass, AE.inner_map_map, AS.norm_map]

/-- the transported operator `AE ∘ X ∘ AE⁻¹`. -/
def conjOp (AE : E ≃ₗᵢ[ℝ] E) (X : E →L[ℝ] E) : E →L[ℝ] E :=
  AE.toContinuousLinearEquiv.conjContinuousAlgEquiv X

theorem conjOp_apply (X : E →L[ℝ] E) (x : E) : conjOp AE X (AE x) = AE (X x) := by
  show AE (X (AE.symm (AE x))) = AE (X x)
  rw [AE.symm_apply_apply]

theorem isG1inv (h : BaseEqv AE AS AF D D') {X : E →L[ℝ] E} (hX : D.IsG1inv X) :
    D'.IsG1inv (conjOp AE X) := by
  refine ⟨fun x y => ?_, fun A => ?_⟩
  · obtain ⟨x, rfl⟩ := AE.surjective x
    obtain ⟨y, rfl⟩ := AE.surjective y
    rw [conjOp_apply, conjOp_apply, AE.inner_map_map, AE.inner_map_map, hX.symm]
  · obtain ⟨A, rfl⟩ := AE.surjective A
    rw [conjOp_apply, AE.inner_map_map, hX.form, h.K]

/-- every `G₁⁻¹` of `D'` is the transport of every `G₁⁻¹` of `D` (via `G1inv_unique`). -/
theorem G1inv (h : BaseEqv AE AS AF D D') {X X' : E →L[ℝ] E} (hX : D.IsG1inv X)
    (hX' : D'.IsG1inv X') (x : E) : X' (AE x) = AE (X x) := by
  rw [D'.G1inv_unique hX' (h.isG1inv hX), conjOp_apply]

theorem G1 (h : BaseEqv AE AS AF D D') {X X' : E →L[ℝ] E} (hX : D.IsG1inv X)
    (hX' : D'.IsG1inv X') (x : E) : D'.G1 X' (AE x) = AE (D.G1 X x) :=
  ringInverse_intertwine AE.toContinuousLinearEquiv (fun y => h.G1inv hX hX' y) x

theorem H1 (h : BaseEqv AE AS AF D D') {X X' : E →L[ℝ] E} (hX : D.IsG1inv X)
    (hX' : D'.IsG1inv X') (f : F) : D'.H1 X' (AF f) = AE (D.H1 X f) :=
  h.Hgen (fun x => h.G1 hX hX' x) f

/-- `Q G₁ Q*` on `F` is `AF`-equivariant. -/
theorem QG1Qs (h : BaseEqv AE AS AF D D') {X X' : E →L[ℝ] E} (hX : D.IsG1inv X)
    (hX' : D'.IsG1inv X') (f : F) :
    D'.Q (D'.G1 X' (D'.Qs (AF f))) = AF (D.Q (D.G1 X (D.Qs f))) := by
  rw [h.Qs, h.G1 hX hX', h.Q]

end BaseEqv

#print axioms conj_ringInverse
#print axioms ringInverse_intertwine
#print axioms BaseEqv.Ts
#print axioms BaseEqv.Qs
#print axioms BaseEqv.Ginv
#print axioms BaseEqv.G
#print axioms BaseEqv.H
#print axioms BaseEqv.K
#print axioms BaseEqv.isG1inv
#print axioms BaseEqv.G1inv
#print axioms BaseEqv.G1
#print axioms BaseEqv.H1
#print axioms BaseEqv.QG1Qs

end AdalyFormal.GaugeCov
