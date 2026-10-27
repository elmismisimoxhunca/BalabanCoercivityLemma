import LoopWords
import T1MainSegment
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 10000
namespace HConstruction.G0Final.Locality
open HConstruction.SmallNF
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)

abbrev Output := CoarseBond witnessL (1*2)
abbrev Site := PeriodicLatticeSite witnessL

def exponentCount (c : Output) (n : ℤ) : ℕ :=
  ((stepBlockOf c.1.1 1 2).filter (fun x => loopWord c x = n)).card

def rowData (c : Output) : ℕ × ℕ × ℕ × ℕ × ℤ :=
  (wordCount c.1.1 [c.2,c.2], exponentCount c (-1), exponentCount c 0,
   exponentCount c 1, ∑ x ∈ stepBlockOf c.1.1 1 2, loopWord c x)

def activeRows : Finset Output :=
  {coarseOutput 0 0 0 0, coarseOutput 0 0 0 1, coarseOutput 0 0 0 2,
   coarseOutput 0 0 1 2, coarseOutput 0 1 0 1}

theorem table_000_0 : rowData (coarseOutput 0 0 0 0) = (1,6,2,0,-6) := by decide +kernel
#print axioms table_000_0
theorem table_000_1 : rowData (coarseOutput 0 0 0 1) = (0,0,7,1,1) := by decide +kernel
#print axioms table_000_1
theorem table_000_2 : rowData (coarseOutput 0 0 0 2) = (0,0,7,1,1) := by decide +kernel
#print axioms table_000_2
theorem table_001_2 : rowData (coarseOutput 0 0 1 2) = (0,1,7,0,-1) := by decide +kernel
#print axioms table_001_2
theorem table_010_1 : rowData (coarseOutput 0 1 0 1) = (0,1,7,0,-1) := by decide +kernel
#print axioms table_010_1

theorem inactive_zero : ∀ (a b d : Fin 2) (mu : Fin 3),
    coarseOutput a b d mu ∉ activeRows →
    ∀ x ∈ stepBlockOf (coarseOutput a b d mu).1.1 1 2,
      loopWord (coarseOutput a b d mu) x = 0 := by decide +kernel

theorem output_parametrization : ∀ c : Output,
    ∃ (a b d : Fin 2) (mu : Fin 3), c = coarseOutput a b d mu := by decide +kernel

theorem other_rows_zero (c : Output) (hc : c ∉ activeRows) :
    ∀ x ∈ stepBlockOf c.1.1 1 2, loopWord c x = 0 := by
  obtain ⟨a,b,d,mu,rfl⟩ := output_parametrization c
  exact inactive_zero a b d mu hc

theorem activeRows_card : activeRows.card = 5 := by decide +kernel

-- The source uses a subtype at stride 1; the loop source uses raw sites.
theorem unitSites_image : ∀ c : Output,
    (unitSitesOf 1 (1*2) c.1.1).image Subtype.val = stepBlockOf c.1.1 1 2 := by decide +kernel

theorem sum_unitSites {M : Type*} [AddCommMonoid M] (c : Output) (f : Site → M) :
    (∑ u ∈ unitSitesOf 1 (1*2) c.1.1, f u.1) =
    ∑ x ∈ stepBlockOf c.1.1 1 2, f x := by
  rw [← unitSites_image c]
  exact (Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)).symm

#print axioms inactive_zero
#print axioms output_parametrization
#print axioms other_rows_zero
#print axioms activeRows_card
#print axioms unitSites_image
#print axioms sum_unitSites
end HConstruction.G0Final.Locality
