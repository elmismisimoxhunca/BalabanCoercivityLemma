import LoopTable
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 10000
namespace HConstruction.G0Final.Locality
open HConstruction.SmallNF
open HConstruction.NfRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.TowerLawCov
open AdalyFormal.Balaban.UbarTowerCov (cPlusS)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

def exceptionalRows : Finset Output := insert (coarseOutput 1 0 0 0) activeRows

/-- Counts occurrences, not net loop exponents: no cancellation of a forward
and inverse factor is used. Includes BOTH the loop source's translated path
and term4's actual recomputed partner path. -/
def derivativePathCount (c : Output) (x : Site) : ℕ :=
  wordCount c.1.1 (coarseGammaPath 1 c.1.1 x) +
  wordCount x [c.2,c.2] +
  wordCount (cPlusS 1 2 (c.1.1,c.2)) (coarseGammaPath 1 c.1.1 x) +
  wordCount c.1.1 [c.2,c.2] +
  wordCount (OneStep124.cPlus c)
    (coarseGammaPath 1 (OneStep124.cPlus c) (OneStep124.partner c x))

theorem derivative_paths_supported : ∀ (a b d : Fin 2) (mu : Fin 3),
    coarseOutput a b d mu ∉ exceptionalRows →
    ∀ x ∈ stepBlockOf (coarseOutput a b d mu).1.1 1 2,
      derivativePathCount (coarseOutput a b d mu) x = 0 := by decide +kernel

theorem other_derivative_paths_zero (c : Output) (hc : c ∉ exceptionalRows) :
    ∀ x ∈ stepBlockOf c.1.1 1 2, derivativePathCount c x = 0 := by
  obtain ⟨a,b,d,mu,rfl⟩ := output_parametrization c
  exact derivative_paths_supported a b d mu hc

theorem exceptionalRows_card : exceptionalRows.card = 6 := by decide +kernel

theorem exceptionalRows_exact : ∀ (a b d : Fin 2) (mu : Fin 3),
    coarseOutput a b d mu ∈ exceptionalRows ↔
      ∃ x ∈ stepBlockOf (coarseOutput a b d mu).1.1 1 2,
        derivativePathCount (coarseOutput a b d mu) x ≠ 0 := by decide +kernel

/-- This sixth row has zero loop exponents but DOES traverse the special bond. -/
theorem sixth_row_witness :
    ∃ x ∈ stepBlockOf (coarseOutput 1 0 0 0).1.1 1 2,
      derivativePathCount (coarseOutput 1 0 0 0) x ≠ 0 ∧
      loopWord (coarseOutput 1 0 0 0) x = 0 := by decide +kernel

def specialEndpoint : Site := ![(1 : Fin 4),0,0]

theorem tree_word_support : ∀ (a b d : Fin 2),
    ∀ x ∈ stepBlockOf (coarseOutput a b d 0).1.1 1 2,
    wordCount (coarseOutput a b d 0).1.1
      (coarseGammaPath 1 (coarseOutput a b d 0).1.1 x) =
      if (coarseOutput a b d 0).1.1 = witnessY ∧ x = specialEndpoint then 1 else 0 := by
  decide +kernel

theorem tree_word_support_output (c : Output) (x : Site)
    (hx : x ∈ stepBlockOf c.1.1 1 2) :
    wordCount c.1.1 (coarseGammaPath 1 c.1.1 x) =
      if c.1.1 = witnessY ∧ x = specialEndpoint then 1 else 0 := by
  obtain ⟨a,b,d,mu,rfl⟩ := output_parametrization c
  exact tree_word_support a b d x hx

/-- An actual source line-integral identity, uniform in t and the input field.
Absence of the special bond makes every recursive transport flat. -/
theorem lineIntegral_eq_flat_of_wordCount_zero (t : ℝ)
    (A : CoarseBond witnessL 1 → SuTwo) (y : Site) (p : List (Fin 3))
    (h : wordCount y p = 0) :
    OneStep124.lineIntegral 1 (nonflatU t) A y p =
      OneStep124.lineIntegral 1 (fun _ => 1) A y p := by
  induction p generalizing y with
  | nil => rfl
  | cons mu p ih =>
    have hz : (if (y,mu)=(witnessY,0) then 1 else 0) = 0 ∧
        wordCount (AdalyFormal.Balaban.CoarseCurl.coarseShift y 1 mu) p = 0 :=
      Nat.add_eq_zero_iff.mp h
    have hn : (y,mu) ≠ (witnessY,0) := by
      intro he
      simp [he] at hz
    simp only [OneStep124.lineIntegral_cons, nonflatU_elsewhere t hn, ih _ hz.2]

theorem holonomy_eq_one_of_wordCount_zero (t : ℝ) (y : Site) (p : List (Fin 3))
    (h : wordCount y p = 0) : coarsePathHolonomy 1 (nonflatU t) y p = 1 := by
  rw [path_word, h, pow_zero]

#print axioms derivative_paths_supported
#print axioms other_derivative_paths_zero
#print axioms exceptionalRows_card
#print axioms exceptionalRows_exact
#print axioms sixth_row_witness
#print axioms tree_word_support
#print axioms tree_word_support_output
#print axioms lineIntegral_eq_flat_of_wordCount_zero
#print axioms holonomy_eq_one_of_wordCount_zero
end HConstruction.G0Final.Locality
