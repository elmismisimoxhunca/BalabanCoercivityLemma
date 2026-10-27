/-! Cofinal bookkeeping consuming dictionary/nonvanishing R3's compiled physical
jet-to-curl theorem. No new proof of that theorem is duplicated here. -/
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative (uthPath vacA)
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Round10.Dictionary.JetDetection
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- These units are known in round 9; kept explicit in the compact harness. -/
def FlatConstraintUnits : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R → IsUnit (Dictionary.KKT.N (flatData q R))

/-- New geometric hand-off: nonzero aggregate at ONE actual block, together with
whole-kernel containment, at nested cofinal scales. This proposition is NOT proved. -/
def CofinalJetLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R, R2.KernelLine (2^j) R (uthPath (2^j) R) u ∧
      ∃ (i : ℕ) (hi : i < blockCount (2^j) R),
        physicalJetAggregate (q := 2^j) (by positivity) hi u ≠ 0

def CofinalAnyPathJetLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ u : TwistSpace (2^j) R, R2.KernelLine (2^j) R V u ∧
        ∃ (i : ℕ) (hi : i < blockCount (2^j) R),
          physicalJetAggregate (q := 2^j) (by positivity) hi u ≠ 0

theorem cofinalCurlLine_of_jetLine (hN : FlatConstraintUnits) (h : CofinalJetLine) :
    CofinalCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,fun R₀ => ?_⟩
  obtain ⟨R,hRR,hR,hR18,u,hline,i,hi,hjet⟩ := hRs R₀
  refine ⟨R,hRR,hR,hR18,u,hline,?_⟩
  exact curlDetected_of_physicalJet (by positivity) (by omega)
    (hN (2^j) R (by positivity) hR hR18) hi u hjet

theorem cofinalAnyPathCurlLine_of_jetLine (hN : FlatConstraintUnits)
    (h : CofinalAnyPathJetLine) : CofinalAnyPathCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,fun R₀ => ?_⟩
  obtain ⟨R,hRR,hR,hR18,V,hVc,hVa,hV0,hneg,u,hline,i,hi,hjet⟩ := hRs R₀
  refine ⟨R,hRR,hR,hR18,V,hVc,hVa,hV0,hneg,u,hline,?_⟩
  exact curlDetected_of_physicalJet (by positivity) (by omega)
    (hN (2^j) R (by positivity) hR hR18) hi u hjet

#print axioms FlatConstraintUnits
#print axioms CofinalJetLine
#print axioms CofinalAnyPathJetLine
#print axioms cofinalCurlLine_of_jetLine
#print axioms cofinalAnyPathCurlLine_of_jetLine
end AdalyFormal.Round10.Assembly.R3
