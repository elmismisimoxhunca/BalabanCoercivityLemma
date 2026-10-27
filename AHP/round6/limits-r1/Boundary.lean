
namespace AdalyFormal.Round6.Guarded.LimitsR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.D1Literal (sing)

/-- The exact outgoing boundary-bond vector used in the negative-endpoint
proof, not an asserted eigenvector or crossing vector. -/
noncomputable def rightVector {q : ℕ} (hq : 0 < q) (R : ℕ) (X : SuTwo) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  ⟨sing (rightSite hq R, (0 : Fin 3)) X,
    AdalyFormal.D1Literal.sing_mem_bondSupp _ (rightSite_bd hq R).hx X⟩

/-- Exact invisibility of the endpoint's bare boundary direction, at EVERY
curvature amplitude, mass, and exterior angle.  This does not assert that a
crossing mode stays supported on that bond. -/
theorem twistD_rightVector_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a t : ℝ) (X : SuTwo) :
    twistD q R ε a t (rightVector hq R X) = 0 := by
  apply AdalyFormal.Round3.Guarded.R2Prove.correction_kills_of_jet_translation
    (dataS selIn selIn (twistP q R ε a t)) (dataS_laws selIn selIn _)
  intro z
  change C2fullOf (geomOf 2 1 (dilTower q R)) (twistU q R ε t)
      (Wop (geomOf 2 1 (dilTower q R)) (twistU q R ε t) a
        (iE _ (z + rightVector hq R X))) =
    C2fullOf (geomOf 2 1 (dilTower q R)) (twistU q R ε t)
      (Wop (geomOf 2 1 (dilTower q R)) (twistU q R ε t) a (iE _ z))
  apply AdalyFormal.StatementLaneR8.C2fullOf_congr_in
    (dil_admissible hq hR) (by norm_num) hroom
  intro e he
  have hne : e ≠ (rightSite hq R, (0 : Fin 3)) := by
    intro hh
    subst e
    exact (rightSite_bd hq R).hx' he.2
  have hz := AdalyFormal.D1Literal.sing_apply_ne
    (rightSite hq R, (0 : Fin 3)) X hne
  have hw : Wop (geomOf 2 1 (dilTower q R)) (twistU q R ε t) a
      (iE _ (rightVector hq R X)) = sing (rightSite hq R, (0 : Fin 3)) X :=
    AdalyFormal.D1Literal.Wop_sing (dil_admissible hq hR) (by omega)
      (rightSite_bd hq R) _ a X
  simp only [map_add, hw, PiLp.add_apply, hz, add_zero]

/-- Symmetry upgrades the vanishing vector to exact orthogonality to the
entire range of the genuine correction.  This is still the bare boundary
vector, not the exact first-crossing kernel. -/
theorem rightVector_orthogonal_correction_range {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) (ε a t : ℝ)
    (X : SuTwo) (y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪rightVector hq R X, twistD q R ε a t y⟫ = 0 := by
  have hs := ((dataS selIn selIn (twistP q R ε a t)).Delta2_spec
    (dataS_laws selIn selIn _)).1 (rightVector hq R X) y
  change ⟪twistD q R ε a t (rightVector hq R X), y⟫ =
    ⟪rightVector hq R X, twistD q R ε a t y⟫ at hs
  rw [← hs, twistD_rightVector_zero hq hR hroom ε a t X, inner_zero_left]

#print axioms rightVector
#print axioms twistD_rightVector_zero
#print axioms rightVector_orthogonal_correction_range
end AdalyFormal.Round6.Guarded.LimitsR1
