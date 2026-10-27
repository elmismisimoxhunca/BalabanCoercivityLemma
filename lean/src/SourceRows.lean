import PathSupport
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
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov
open AdalyFormal.Balaban.UbarTowerCov (cPlusS)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

def blockOffsets : List (Fin 3 → Fin 2) :=
  [![(0 : Fin 2),0,0], ![0,0,1], ![0,1,0], ![0,1,1],
   ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]]

#print axioms blockOffsets

def blockPoint (c : Output) (u : Fin 3 → Fin 2) : Site :=
  fun mu => c.1.1 mu + ((u mu).castLE (by fin_cases mu <;> decide) : Fin (witnessL mu + 1))

#print axioms blockPoint

def rowWords (c : Output) : List ℤ :=
  blockOffsets.map (fun u => loopWord c (blockPoint c u))

theorem blockPoints_exact : ∀ c : Output,
    (blockOffsets.map (blockPoint c)).toFinset = stepBlockOf c.1.1 1 2 := by decide +kernel

#print axioms blockPoints_exact

theorem blockPoints_nodup : ∀ c : Output,
    (blockOffsets.map (blockPoint c)).Nodup := by decide +kernel

#print axioms blockPoints_nodup

theorem rowWords_000_0 : rowWords (coarseOutput 0 0 0 0) = [0,-1,-1,-1,0,-1,-1,-1] := by decide +kernel
theorem rowWords_000_1 : rowWords (coarseOutput 0 0 0 1) = [0,0,0,0,1,0,0,0] := by decide +kernel
theorem rowWords_000_2 : rowWords (coarseOutput 0 0 0 2) = [0,0,0,0,1,0,0,0] := by decide +kernel
theorem rowWords_001_2 : rowWords (coarseOutput 0 0 1 2) = [0,0,0,0,-1,0,0,0] := by decide +kernel
theorem rowWords_010_1 : rowWords (coarseOutput 0 1 0 1) = [0,0,0,0,-1,0,0,0] := by decide +kernel

#print axioms rowWords_010_1

/-- Rational mean of the integer exponents over the ACTUAL coefficient summation set.
This is not an assertion about principal logarithms. -/
def unitExponentMean (c : Output) : ℚ :=
  (∑ u ∈ unitSitesOf 1 (1*2) c.1.1, (loopWord c u.1 : ℚ)) / 8

theorem unitSites_card : ∀ c : Output, (unitSitesOf 1 (1*2) c.1.1).card = 8 := by decide +kernel

#print axioms unitSites_card

theorem mean_000_0 : unitExponentMean (coarseOutput 0 0 0 0) = -3/4 := by decide +kernel
theorem mean_000_1 : unitExponentMean (coarseOutput 0 0 0 1) = 1/8 := by decide +kernel
theorem mean_000_2 : unitExponentMean (coarseOutput 0 0 0 2) = 1/8 := by decide +kernel
theorem mean_001_2 : unitExponentMean (coarseOutput 0 0 1 2) = -1/8 := by decide +kernel
theorem mean_010_1 : unitExponentMean (coarseOutput 0 1 0 1) = -1/8 := by decide +kernel

theorem mean_other (c : Output) (hc : c ∉ activeRows) : unitExponentMean c = 0 := by
  unfold unitExponentMean
  rw [sum_unitSites c (fun x => (loopWord c x : ℚ))]
  have hsum : (∑ x ∈ stepBlockOf c.1.1 1 2, (loopWord c x : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [other_rows_zero c hc x hx, Int.cast_zero]
  rw [hsum, zero_div]

theorem derivative_path_components_zero (c : Output) (x : Site)
    (hc : c ∉ exceptionalRows) (hx : x ∈ stepBlockOf c.1.1 1 2) :
    wordCount c.1.1 (coarseGammaPath 1 c.1.1 x) = 0 ∧
    wordCount x [c.2,c.2] = 0 ∧
    wordCount (cPlusS 1 2 (c.1.1,c.2)) (coarseGammaPath 1 c.1.1 x) = 0 ∧
    wordCount c.1.1 [c.2,c.2] = 0 ∧
    wordCount (OneStep124.cPlus c)
      (coarseGammaPath 1 (OneStep124.cPlus c) (OneStep124.partner c x)) = 0 := by
  have h := other_derivative_paths_zero c hc x hx
  unfold derivativePathCount at h
  omega

/-- The four line integrals occurring in the actual five-channel formula are
flat off the six rows, for EVERY input, not merely at the background value. -/
theorem source_lineIntegrals_flat (t : ℝ) (A : CoarseBond witnessL 1 → SuTwo)
    (c : Output) (x : Site) (hc : c ∉ exceptionalRows)
    (hx : x ∈ stepBlockOf c.1.1 1 2) :
    OneStep124.lineIntegral 1 (nonflatU t) A c.1.1 (coarseGammaPath 1 c.1.1 x) =
      OneStep124.lineIntegral 1 (fun _ => 1) A c.1.1 (coarseGammaPath 1 c.1.1 x) ∧
    OneStep124.lineIntegral 1 (nonflatU t) A x [c.2,c.2] =
      OneStep124.lineIntegral 1 (fun _ => 1) A x [c.2,c.2] ∧
    OneStep124.lineIntegral 1 (nonflatU t) A (OneStep124.cPlus c)
        (coarseGammaPath 1 (OneStep124.cPlus c) (OneStep124.partner c x)) =
      OneStep124.lineIntegral 1 (fun _ => 1) A (OneStep124.cPlus c)
        (coarseGammaPath 1 (OneStep124.cPlus c) (OneStep124.partner c x)) ∧
    OneStep124.lineIntegral 1 (nonflatU t) A c.1.1 [c.2,c.2] =
      OneStep124.lineIntegral 1 (fun _ => 1) A c.1.1 [c.2,c.2] := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := derivative_path_components_zero c x hc hx
  exact ⟨lineIntegral_eq_flat_of_wordCount_zero t A _ _ h1,
    lineIntegral_eq_flat_of_wordCount_zero t A _ _ h2,
    lineIntegral_eq_flat_of_wordCount_zero t A _ _ h5,
    lineIntegral_eq_flat_of_wordCount_zero t A _ _ h4⟩

theorem tree_holonomy (t : ℝ) (c : Output) (x : Site)
    (hx : x ∈ stepBlockOf c.1.1 1 2) :
    coarsePathHolonomy 1 (nonflatU t) c.1.1 (coarseGammaPath 1 c.1.1 x) =
      if c.1.1 = witnessY ∧ x = specialEndpoint then rotElem t else 1 := by
  rw [path_word, tree_word_support_output c x hx]
  split <;> simp

#print axioms blockPoints_exact
#print axioms blockPoints_nodup
#print axioms rowWords_000_0
#print axioms rowWords_000_1
#print axioms rowWords_000_2
#print axioms rowWords_001_2
#print axioms rowWords_010_1
#print axioms unitSites_card
#print axioms mean_000_0
#print axioms mean_000_1
#print axioms mean_000_2
#print axioms mean_001_2
#print axioms mean_010_1
#print axioms mean_other
#print axioms derivative_path_components_zero
#print axioms source_lineIntegrals_flat
#print axioms tree_holonomy
end HConstruction.G0Final.Locality
