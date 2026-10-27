namespace AdalyFormal.Round3.Guarded.R2Prove

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round2.Guarded.R2Prove
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section Algebra
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Translation invisibility for the genuine quadratic jet kills the full
correction vector, not just its diagonal pairing. -/
theorem correction_kills_of_jet_translation (D : BaseDataS E S F) (hL : D.Laws)
    (x : E) (hjet : ∀ z : E, D.C2 (z + x) = D.C2 z) :
    D.Delta2 hL x = 0 := by
  obtain ⟨hs, hf⟩ := D.Delta2_spec hL
  have hx := hf x
  have hz := hf 0
  have hcx : D.C2 x = D.C2 0 := by simpa only [zero_add] using hjet 0
  rw [hcx] at hx
  have hdiag : ⟪x, D.Delta2 hL x⟫ = 0 := by
    simpa only [inner_zero_left] using hx.trans hz.symm
  apply ext_inner_left ℝ
  intro z
  have hsum := hf (z + x)
  rw [hjet z, ← hf z] at hsum
  have hsym : ⟪x, D.Delta2 hL z⟫ = ⟪z, D.Delta2 hL x⟫ := by
    rw [real_inner_comm, hs]
  simp only [map_add, inner_add_left, inner_add_right, hsym, hdiag] at hsum
  rw [inner_zero_right]
  linarith

end Algebra

#print axioms correction_kills_of_jet_translation
end AdalyFormal.Round3.Guarded.R2Prove
