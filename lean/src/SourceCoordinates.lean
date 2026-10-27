import SourceCompression
import CircleActions

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.G0HSchur
open HConstruction.Covariance HConstruction.SmallNF HConstruction.Carrier
open HConstruction.Circle
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

/-- Exact normalized Pauli basis, not the ambient matrix Frobenius norm. -/
def fibreBasis : OrthonormalBasis (Fin 3) ℝ SuTwo :=
  OrthonormalBasis.ofRepr coordinateIsometry

abbrev FineIndex := (b : Bond witnessL) × Fin 3
abbrev SiteIndex := (s : PeriodicLatticeSite witnessL) × Fin 3
abbrev CoarseIndex := (c : CoarseBond witnessL (1*2)) × Fin 3

def fineBasis : OrthonormalBasis FineIndex ℝ H :=
  Pi.orthonormalBasis (fun _ : Bond witnessL => fibreBasis)

def siteBasis : OrthonormalBasis SiteIndex ℝ S :=
  Pi.orthonormalBasis (fun _ : PeriodicLatticeSite witnessL => fibreBasis)

def coarseBasis : OrthonormalBasis CoarseIndex ℝ K :=
  Pi.orthonormalBasis (fun _ : CoarseBond witnessL (1*2) => fibreBasis)

@[simp] theorem fine_repr (A : H) (b : Bond witnessL) (i : Fin 3) :
    fineBasis.repr A ⟨b,i⟩ = coordinateIsometry (bfl2Equiv A b) i := rfl

@[simp] theorem site_repr (A : S) (s : PeriodicLatticeSite witnessL) (i : Fin 3) :
    siteBasis.repr A ⟨s,i⟩ = coordinateIsometry (fiberEquiv _ A s) i := rfl

@[simp] theorem coarse_repr (A : K) (c : CoarseBond witnessL (1*2)) (i : Fin 3) :
    coarseBasis.repr A ⟨c,i⟩ = coordinateIsometry (cfl2Equiv 2 A c) i := rfl

/-- The full product coordinate maps are isometries on the original carriers. -/
theorem fine_norm (A : H) : ‖fineBasis.repr A‖ = ‖A‖ := fineBasis.repr.norm_map A

theorem site_norm (A : S) : ‖siteBasis.repr A‖ = ‖A‖ := siteBasis.repr.norm_map A

theorem coarse_norm (A : K) : ‖coarseBasis.repr A‖ = ‖A‖ := coarseBasis.repr.norm_map A

#print axioms fine_repr
#print axioms site_repr
#print axioms coarse_repr
#print axioms fine_norm
#print axioms site_norm
#print axioms coarse_norm
end HConstruction.G0HSchur
