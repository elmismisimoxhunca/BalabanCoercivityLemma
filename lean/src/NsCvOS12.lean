import NsCvOS11
import NsCvON5

/-!
# CvOS12 -- the proxy `Dstruct` for the nested staggered family, and its unit property (lane omega/near2/struct)

`DstructP P = DstructG P.G P.U P.a P.sector P.Jf`; `DstructP_ne_iff`: `≠ 0 ↔ gOf ≠ 0 ∧ UnitsFour P` (site outside `Om0`).
`Dstruct ell M R hell a t = DstructP (gparams .. (stagU ell M R t) ..)`.
`anUnits4_of_dstruct`: analytic on `(-tcap ell, tcap ell)` and nonzero somewhere gives `AnUnits4`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverOmega (UnitsFour AnUnits4 stagU)

/-- the structural proxy of an `IngrBParams`. -/
noncomputable def DstructP (P : IngrBParams) : ℝ := DstructG P.G P.U P.a P.sector P.Jf

theorem unitsFour_iff_BDUnits (P : IngrBParams) : UnitsFour P ↔ BDUnits P.data P.data_laws := by
  have hG1 : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  unfold UnitsFour BDUnits GenP.Nmat
  rw [hG1]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h3, h4, h1, h2⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h3, h4, h1, h2⟩

theorem DstructP_ne_iff (P : IngrBParams) (hout : ∃ x : PeriodicLatticeSite (scaleUp P.ell P.k P.Lu), x ∉ P.G.Om0) :
    DstructP P ≠ 0 ↔ gOf P.G P.U ≠ 0 ∧ UnitsFour P := by
  rw [unitsFour_iff_BDUnits]
  exact DstructG_ne_iff P.G P.U P.a P.sector P.Jf hout

/-- the parameters of the nested staggered family at `t`. -/
noncomputable def PN (ell M R : ℕ) (hell : 0 < ell) (a t : ℝ) : IngrBParams :=
  gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R)

noncomputable def Dstruct (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (t : ℝ) : ℝ := DstructP (PN ell M R hell a t)

theorem out_nested {ell M R : ℕ} (hell3 : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hell : 0 < ell) (a t : ℝ) :
    ∃ x : PeriodicLatticeSite (scaleUp (PN ell M R hell a t).ell (PN ell M R hell a t).k (PN ell M R hell a t).Lu),
      x ∉ (PN ell M R hell a t).G.Om0 := by
  refine ⟨fun _ => 0, fun hmem => ?_⟩
  simp only [PN, gparams, geomOf, Set.mem_setOf_eq] at hmem
  have h0 := ((neS_om0 (ell := ell) (M := M) (R := R) (fun _ => 0)).mp hmem).1
  have hp := ne_P0_pos hell3 hM hR
  simp at h0
  omega

/-- **the unit property of the proxy**: `Dstruct t ≠ 0` gives the four units. -/
theorem dstruct_units {ell M R : ℕ} (hell3 : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hell : 0 < ell) (a t : ℝ)
    (h : Dstruct ell M R hell a t ≠ 0) : UnitsFour (PN ell M R hell a t) :=
  ((DstructP_ne_iff _ (out_nested hell3 hM hR hell a t)).mp h).2

/-- **converse**: `g ≠ 0` and the four units give `Dstruct t ≠ 0` (so a unit result at one point is a nonvanishing point). -/
theorem dstruct_ne_zero_of_units {ell M R : ℕ} (hell3 : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hell : 0 < ell) (a t : ℝ)
    (hg : gOf (PN ell M R hell a t).G (PN ell M R hell a t).U ≠ 0) (hu : UnitsFour (PN ell M R hell a t)) :
    Dstruct ell M R hell a t ≠ 0 :=
  (DstructP_ne_iff _ (out_nested hell3 hM hR hell a t)).mpr ⟨hg, hu⟩

/-- **composition with the generic-in-`t` reduction**: analytic proxy nonzero somewhere gives `AnUnits4`. -/
theorem anUnits4_of_dstruct {ell M R : ℕ} (hell3 : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hell : 0 < ell) (a : ℝ)
    (hana : AnalyticOnNhd ℝ (Dstruct ell M R hell a) (Ioo (-tcap ell) (tcap ell)))
    (h0 : ∃ t0 ∈ Ioo (-tcap ell) (tcap ell), Dstruct ell M R hell a t0 ≠ 0) : AnUnits4 ell M R hell a :=
  ⟨Dstruct ell M R hell a, hana, h0, fun t _ ht => dstruct_units hell3 hM hR hell a t ht⟩

#print axioms DstructP_ne_iff
#print axioms dstruct_units
#print axioms dstruct_ne_zero_of_units
#print axioms anUnits4_of_dstruct

end AdalyFormal.CoverOmega.Struct
