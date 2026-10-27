import SG15
import SK7

/-!
# SG16 -- the skeleton with fields F1-F3 replaced (lane m2_fields123_20261015)

`target8_of_goodAll` : `GoodAll` plus the OTHER three fields of `RemainingInputs` (`interfaceCharts`, `opLayer`, `qsInj`, taken from any `RI : RemainingInputs`)
give the frozen r8 headline `P428Target8`.  The `siteS1`, `rowBound`, `massComm` components of `RI` are not used.
-/
set_option autoImplicit false
namespace AdalyFormal.M2F123

open AdalyFormal.M2Skel

theorem target8_of_goodAll (hG : GoodAll) (RI : RemainingInputs) : AdalyFormal.StatementLaneG.P428Target8 :=
  p428Target8_of_parts
    { RI with
      siteS1 := fun ell hell a ha => (fields123_of_goodAll hG).1 ell hell a ha
      rowBound := fun ell hell a ha => (fields123_of_goodAll hG).2.1 ell hell a ha
      massComm := fun ell hell a ha => (fields123_of_goodAll hG).2.2 ell hell a ha }

end AdalyFormal.M2F123

#print axioms AdalyFormal.M2F123.target8_of_goodAll
