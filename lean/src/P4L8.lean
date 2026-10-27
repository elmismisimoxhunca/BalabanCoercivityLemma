import P4L7
import Lean
/-!
# P4L8 -- STATEMENT-CLOSURE check.  For each headline, list every non-library DEFINITION reachable from the STATEMENT (type) by unfolding definition bodies,
with the module that defines it.  (Library = module name starting Init/Std/Lean/Mathlib/Batteries/Aesop/Qq/Plausible/ProofWidgets/ImportGraph/LeanSearchClient.)
Output is printed to the build log and saved to gate_record/statement_closure.txt.
-/
open Lean Meta Elab Command

def libPrefixes : List String := ["Init", "Std", "Lean", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient"]

def isLibMod (m : Name) : Bool := libPrefixes.any (fun p => (m.getRoot.toString == p))

partial def stmtClosure (env : Environment) (todo : List Name) (seen : NameSet) (acc : Array Name) : NameSet × Array Name :=
  match todo with
  | [] => (seen, acc)
  | n :: rest =>
    if seen.contains n then stmtClosure env rest seen acc else
    let seen := seen.insert n
    match env.find? n with
    | none => stmtClosure env rest seen acc
    | some ci =>
      let modName : Name := match env.getModuleIdxFor? n with
        | some i => env.header.moduleNames[i.toNat]!
        | none => `_current
      if isLibMod modName then stmtClosure env rest seen acc
      else
        let tcs := ci.type.getUsedConstants.toList
        let vcs := match ci with
          | .defnInfo d => d.value.getUsedConstants.toList
          | _ => []
        let isDef := match ci with | .defnInfo _ => true | .inductInfo _ => true | _ => false
        let acc := if isDef then acc.push n else acc
        stmtClosure env (tcs ++ vcs ++ rest) seen acc

def headlines : List Name :=
  [``AdalyFormal.P409L.local_print_fails, ``AdalyFormal.P409L.local_window, ``AdalyFormal.P409L.cube5_is_class_box,
   ``AdalyFormal.P409L.local_in_class_box, ``AdalyFormal.P409L.local_in_union, ``AdalyFormal.P409L.j0_print_holds,
   ``AdalyFormal.P409L.j0_p396_fails, ``AdalyFormal.P409L.tg_nonvacuous, ``AdalyFormal.P409L.localHalf_le_six,
   ``AdalyFormal.P409L.anyr0_print_fails, ``AdalyFormal.P409L.local_box_window, ``AdalyFormal.P409L.tg_aligned_lower]

run_cmd do
  let env ← getEnv
  for h in headlines do
    match env.find? h with
    | none => logInfo m!"MISSING {h}"
    | some ci =>
      let (_, acc) := stmtClosure env ci.type.getUsedConstants.toList {} #[]
      let lines := acc.toList.map fun n =>
        let m : Name := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i.toNat]! | none => `_current
        s!"  {n}   [{m}]"
      logInfo m!"HEADLINE {h}: {acc.size} non-library definitions in the statement closure\n{String.intercalate "\n" lines}"
