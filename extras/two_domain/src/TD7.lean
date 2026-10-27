import TD5
import TD6
import Lean

/-!
# TD7 -- gates (lane two_domain_20261019): (1) STATEMENT-CLOSURE of each headline (every non-library definition reachable from the statement, with its defining module);
(2) in-Lean axiom CENSUS over every constant of the modules THL1..THL8 (roots, union of axioms, count of roots with a non-standard axiom).
Output is printed to the build log and saved under gate_record/.
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
  [``AdalyFormal.TwoDom.regBody_mono_b, ``AdalyFormal.TwoDom.glue_side, ``AdalyFormal.TwoDom.regBody_glue, ``AdalyFormal.TwoDom.far_block_exists, ``AdalyFormal.TwoDom.pdist_block_le, ``AdalyFormal.TwoDom.cover_cut, ``AdalyFormal.TwoDom.famTwoDom_union, ``AdalyFormal.TwoDom.descAt0_of_described, ``AdalyFormal.TwoDom.descAlt_congr, ``AdalyFormal.TwoDom.classCoupledCap_of_two, ``AdalyFormal.TwoDom.famTwoDom_cap, ``AdalyFormal.TwoDom.famTwoDom_box, ``AdalyFormal.TwoDom.oneDom_of_twoDom, ``AdalyFormal.TwoDom.oneDomCap_of_twoDom, ``AdalyFormal.TwoDom.totalLayer_of_twoDom, ``AdalyFormal.TwoDom.mixedTwoDom, ``AdalyFormal.TwoDom.totalTwoDom, ``AdalyFormal.TwoDom.target8TwoDom, ``AdalyFormal.TwoDom.two_nonvac_core, ``AdalyFormal.TwoDom.twodom_nonvac_regime, ``AdalyFormal.TwoDom.twodom_instance_inequality, ``AdalyFormal.TwoDom.slabT_two, ``AdalyFormal.TwoDom.regBody_of_M1_union, ``AdalyFormal.TwoDom.classCoupledU_of_M1, ``AdalyFormal.TwoDom.twodom_union_instance_inequality, ``AdalyFormal.TwoDom.plain_cut_fails]

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

run_cmd do
  let env ← getEnv
  let ok : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut roots : Array Name := #[]
  for (md, i) in (env.header.moduleData.toList.zipIdx) do
    let s := (env.header.moduleNames[i]!).toString
    if s.startsWith "TD" && s != "TD7" then
      for nm in md.constNames do
        if !nm.isInternal && !nm.isAnonymous then roots := roots.push nm
  let mut bad : Array Name := #[]
  let mut union : NameSet := {}
  for nm in roots do
    let ax ← liftCoreM (collectAxioms nm)
    for a in ax do union := union.insert a
    if !(ax.all (fun a => ok.contains a)) then bad := bad.push nm
  logInfo m!"CENSUS_AXIOMS roots={roots.size} union_of_axioms={union.toList} roots_with_nonstandard_axioms={bad.size} {bad}"

-- per-headline #print axioms (saved to gate_record/axioms_headlines.txt)
#print axioms AdalyFormal.TwoDom.regBody_mono_b
#print axioms AdalyFormal.TwoDom.glue_side
#print axioms AdalyFormal.TwoDom.regBody_glue
#print axioms AdalyFormal.TwoDom.far_block_exists
#print axioms AdalyFormal.TwoDom.pdist_block_le
#print axioms AdalyFormal.TwoDom.cover_cut
#print axioms AdalyFormal.TwoDom.famTwoDom_union
#print axioms AdalyFormal.TwoDom.descAt0_of_described
#print axioms AdalyFormal.TwoDom.descAlt_congr
#print axioms AdalyFormal.TwoDom.classCoupledCap_of_two
#print axioms AdalyFormal.TwoDom.famTwoDom_cap
#print axioms AdalyFormal.TwoDom.famTwoDom_box
#print axioms AdalyFormal.TwoDom.oneDom_of_twoDom
#print axioms AdalyFormal.TwoDom.oneDomCap_of_twoDom
#print axioms AdalyFormal.TwoDom.totalLayer_of_twoDom
#print axioms AdalyFormal.TwoDom.mixedTwoDom
#print axioms AdalyFormal.TwoDom.totalTwoDom
#print axioms AdalyFormal.TwoDom.target8TwoDom
#print axioms AdalyFormal.TwoDom.two_nonvac_core
#print axioms AdalyFormal.TwoDom.twodom_nonvac_regime
#print axioms AdalyFormal.TwoDom.twodom_instance_inequality
#print axioms AdalyFormal.TwoDom.slabT_two
#print axioms AdalyFormal.TwoDom.regBody_of_M1_union
#print axioms AdalyFormal.TwoDom.classCoupledU_of_M1
#print axioms AdalyFormal.TwoDom.twodom_union_instance_inequality
#print axioms AdalyFormal.TwoDom.plain_cut_fails
