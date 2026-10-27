import SK6

/-!
# SK7 -- the M2 assembly: `p428Target8_of_parts : RemainingInputs → P428Target8` (lane m2_skeleton_20261015)

`P428Target8` is the FROZEN r8 headline (`ZT5A.P428Target8`, re-exported by `TargetContract`), unchanged.
`RemainingInputs` (SK1) lists exactly the six pieces that no committed theorem supplies; see REMAINING.md.
-/
set_option autoImplicit false
namespace AdalyFormal.M2Skel

/-- **the full headline, conditional on the six named inputs**. -/
theorem p428Target8_of_parts (RI : RemainingInputs) : AdalyFormal.StatementLaneG.P428Target8 :=
  fun ell hell a ha => class_core RI hell ha

end AdalyFormal.M2Skel

#print axioms AdalyFormal.M2Skel.p428Target8_of_parts
