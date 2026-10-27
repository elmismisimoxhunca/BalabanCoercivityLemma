/-! Combined actual-operator application of the physical transverse-flux theorem.
The nonzero jet and full flat N unit remain explicit hypotheses. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.JetDetection
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Nonvanishing.DilatedFlux

/-- The fixed norm-one diagonal Pauli coordinate, as a real linear functional. -/
def neutralFunctional : SuTwo →ₗ[ℝ] ℝ where
  toFun := neutralCoord
  map_add' := fun x y => inner_add_right pauliE3 x y
  map_smul' := by
    intro c x
    change ⟪pauliE3, c • x⟫ = c * ⟪pauliE3, x⟫
    exact inner_smul_right _ _ _

/-- Sum of the genuine normalized top jet over all physical even transverse cells.
There is no cell-isometry or cell-normalization assumption in this definition. -/
def physicalJetAggregate {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (u : TwistSpace q R) : ℝ :=
  jetAggregate hq hj neutralFunctional
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) u))

/-- The source-column recurrence is not needed: an aggregated nonzero actual jet
forces detection by an allowed interior profile via the FULL constrained lift. -/
theorem curlDetected_of_physicalJet {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hne : physicalJetAggregate hq hj u ≠ 0) : CurlDetected q R u := by
  let A := iE (geomOf 2 1 (dilTower q R)) ((flatData q R).H (vacJet q R u))
  let v := Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1
    (iE (geomOf 2 1 (dilTower q R)) u)
  have hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg v :=
    liftJet_Q q R hN u
  obtain ⟨p, hp, hc⟩ := localized_curl_of_jetAggregate hq hR hj neutralFunctional A v hQ hne
  exact ⟨p, hp, hc⟩

/-- The specific physical adaptive profile has strictly positive explicit coupling. -/
theorem adaptive_pos_of_physicalJet {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hne : physicalJetAggregate hq hj u ≠ 0) :
    0 < profileCoupling q R (responseProfile q R u) u :=
  (adaptive_pos_iff q R u).mpr (curlDetected_of_physicalJet hq hR hN hj u hne)

/-- A free profile exists, but this does not choose one common profile for a
higher-dimensional kernel. Assembly's whole-kernel criterion is still required. -/
theorem exists_profile_of_physicalJet {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hne : physicalJetAggregate hq hj u ≠ 0) :
    ∃ f, profileCoupling q R f u ≠ 0 :=
  (exists_profile_iff_curlDetected q R u).mpr (curlDetected_of_physicalJet hq hR hN hj u hne)

/-- The two tracks use the same physical aggregate, definitionally. -/
theorem topJetDetected_iff {q : ℕ} (hq : 0 < q) (R : ℕ) (u : TwistSpace q R) :
    TopJetDetected hq R u ↔ ∃ j : ℕ, ∃ hj : j < blockCount q R,
      physicalJetAggregate hq hj u ≠ 0 := Iff.rfl

/-- Final joint hand-off: the only source-detection input left is the genuine
crossing-jet nondegeneracy; no source-column or normalization premise remains. -/
theorem curlDetected_of_topJet {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (u : TwistSpace q R) (hjet : TopJetDetected hq R u) : CurlDetected q R u := by
  obtain ⟨j, hj, hne⟩ := (topJetDetected_iff hq R u).mp hjet
  exact curlDetected_of_physicalJet hq hR hN hj u hne

#print axioms topJetDetected_iff
#print axioms curlDetected_of_topJet
#print axioms neutralFunctional
#print axioms physicalJetAggregate
#print axioms curlDetected_of_physicalJet
#print axioms adaptive_pos_of_physicalJet
#print axioms exists_profile_of_physicalJet
end AdalyFormal.Round10.Dictionary.JetDetection
