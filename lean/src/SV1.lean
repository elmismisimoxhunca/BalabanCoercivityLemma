import TL22a

/-!
# SV1 -- `WellDefG` descends from the cover to the base torus (lane strong_variants_20261016)

`wellDefG_of_coverHyp` : the cover hypothesis `CoverHyp` (units of every inverse in `genForm` AT THE COVER, bijectivity of `H₀` at the
cover, regularity) implies `WellDefG` of the BASE parameters `P0 = gparams ell k Lu hell S U a Lam`.  Every piece is an existing descent
lemma of the thin lane (m2_thin_20261015): `desc_Gp` (unit of `Δ'_a|Ω₀ + (1 - Ω₀)`), `BDLink.G` (unit of `G⁻¹`), the `Q G Q*` descent
(as in `BDLink.H`) + `HDesc.inverse`, `BDLink.G1inv` + `hisUnit_of_he1` (unit of `G₁⁻¹`), `BDLink.Nmat` + `HDesc.inverse` (unit of
`Q G₁ Q*`), `H0inv_nat` (bijectivity of `H₀`).
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
namespace AdalyFormal.StrongVariants
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Thin

section wd
variable {Lut Lu : PeriodicLatticeExtent} {hu : Covers Lut Lu} {ell k : ℕ} {hell : 0 < ell}
variable {S : Tower (scaleUp ell k Lu)} {U : Cfg (scaleUp ell k Lu)} {a : ℝ} {Lam : Set (PeriodicLatticeSite Lu)}

/-- **`WellDefG` at the base torus from the cover hypothesis.** -/
theorem wellDefG_of_coverHyp {hp : PhiOK (covers_scaleUp ell k hell hu) (fun _ => 0) (ell ^ k)}
    (hc : CoverHyp hu hell S U a Lam hp) : GenP.WellDefG (P0 hell S U a Lam) := by
  haveI := deckIdx_nonempty (covers_scaleUp ell k hell hu)
  have bd := hc.bd
  have hG := bd.G hc.ginv
  have hM' := (bd.qs.comp hG.2).comp bd.q
  have hH := bd.H hc.ginv hc.qgqs
  have hG1d := bd.G1inv hH (P0 hell S U a Lam).G1inv_spec (Pt hu hell S U a Lam).G1inv_spec
  have hNd := bd.Nmat hG1d hc.g1inv
  have hpOK : PhiOK hu (fun _ => 0) ell := ⟨hc.hT1, fun _ => dvd_zero _⟩
  have hH0 := (H0inv_nat hpOK hell Lam (Pt hu hell S U a Lam).Q1 (P0 hell S U a Lam).Q1
    (fun B c hcr => Q1_nat hu hell S U a Lam hc.hT1 hp hc.ureg B c hcr) (dmap_surj hu hell Lam hc.hT1) hc.h0 0).1
  refine ⟨⟨hH0, hisUnit_of_he1 hG1d.e1 hc.g1inv, (hNd.inverse hc.nmat).1⟩, ?_, hG.1, (hM'.inverse hc.qgqs).1⟩
  exact (desc_Gp (covers_scaleUp ell k hell hu) hp hell S U a hc.gp).1

end wd

end AdalyFormal.StrongVariants

#print axioms AdalyFormal.StrongVariants.wellDefG_of_coverHyp
