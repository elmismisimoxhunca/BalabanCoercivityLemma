import TT_F
import MXQ_Br
import MXQ_Tor
import DrEquiv

set_option maxHeartbeats 16000000
set_option format.width 100000

run_cmd do
  let env ← Lean.getEnv
  let mut todo : Array Lean.Name := #[`AdalyFormal.Total.p428Target8Total,
    `MXP.Total.p428Target8Mixed, `MXQ.Total.p428Target8FamilyTorus,
    `AdalyFormal.M2RightInv.p428Target8, `AdalyFormal.D1Residual.P428Target8SG_iff_pencilT]
  let mut seen : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let used := ci.type.getUsedConstants ++ ((ci.value? true).map Lean.Expr.getUsedConstants |>.getD #[])
      let deps := used.filter fun d =>
        let s := d.toString
        s.startsWith "AdalyFormal." || s.startsWith "MXP." || s.startsWith "MXQ." || s.startsWith "SmallnessBridge."
      Lean.logInfo m!"DEPENDENCY|{n}|{String.intercalate "," (deps.toList.map Lean.Name.toString)}"
      todo := todo ++ deps

#print axioms AdalyFormal.Total.p428Target8Total
#print axioms MXP.Total.p428Target8Mixed
#print axioms MXQ.Total.p428Target8FamilyTorus
#print axioms AdalyFormal.M2RightInv.p428Target8
#print axioms AdalyFormal.D1Residual.P428Target8SG_iff_pencilT
