import RB3

/-!
# RB4 -- non-vacuity of the printed side, a discriminating instance, `#print axioms` for every headline and the STATEMENT-CLOSURE
(every non-library definition reachable from each headline statement).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

open Lean Meta Elab Command

namespace AdalyFormal.RBridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.P409S

/-- non-vacuity (L7): at `ell = 2, M = 1, R = 1, k = 1` there is a torus and a tower satisfying the printed conditions (and padding),
with every stratum `B^0, B^1` non-empty (transported from the deep witness of the sharp lane through `admissible_iff_print`). -/
theorem printed_nonvacuous :
    ∃ (Lf : PeriodicLatticeExtent) (S : Tower Lf), PrintedTower 2 1 1 1 S ∧ PadAbove 1 S ∧
      (∀ i : ℕ, i ≤ 1 → ∃ q, q ∈ towerBj S i) := by
  obtain ⟨Lf, h1, h2, h3⟩ := torus_hyps_satisfiable 2 1 1 1 (by norm_num) (by norm_num)
  obtain ⟨S, c, hA, -, -, hstr, -⟩ := cube5_fails_below_deep (ell := 2) (M := 1) (R := 1) (k := 1) (j' := 0) (Lf := Lf)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bigSide; norm_num) h1 h2
  exact ⟨Lf, S, ((admissible_iff_print (by norm_num) (by norm_num) S).1 hA).1,
    ((admissible_iff_print (by norm_num) (by norm_num) S).1 hA).2, hstr⟩

/-- the printed predicate discriminates: the tower with every `Omega_j` equal to the whole torus violates `Omega_{k+1} = emptyset`. -/
theorem printed_discriminates : ∃ S : Tower Lw, ¬ PrintedTower 2 1 1 1 S :=
  ⟨⟨fun _ => Set.univ⟩, fun h => by
    have := h.2.1
    have hx : (fun _ => (0 : Fin 8)) ∈ (Set.univ : Set (PeriodicLatticeSite Lw)) := trivial
    rw [show (⟨fun _ => Set.univ⟩ : Tower Lw).Om (1 + 1) = Set.univ from rfl] at this
    rw [this] at hx
    exact hx⟩

end AdalyFormal.RBridge

#print axioms AdalyFormal.RBridge.admissible_iff_print
#print axioms AdalyFormal.RBridge.blockClosed_iff_sum
#print axioms AdalyFormal.RBridge.om0clause_iff_print
#print axioms AdalyFormal.RBridge.collar_iff_rat
#print axioms AdalyFormal.RBridge.om0Print_collar
#print axioms AdalyFormal.RBridge.om0Print_least
#print axioms AdalyFormal.RBridge.om0Print_char
#print axioms AdalyFormal.RBridge.collar0_violated_of_not_sup
#print axioms AdalyFormal.RBridge.om1_sub_om0Print
#print axioms AdalyFormal.RBridge.om0All_collar_imp_eq
#print axioms AdalyFormal.RBridge.om0Lt_collar_imp_eq
#print axioms AdalyFormal.RBridge.om0Lt_eq_rad
#print axioms AdalyFormal.RBridge.om0Print_sub_unit
#print axioms AdalyFormal.RBridge.readings_differ
#print axioms AdalyFormal.RBridge.alt_readings_violate_collar0
#print axioms AdalyFormal.RBridge.cube5_class_box_printed
#print axioms AdalyFormal.RBridge.collar_threshold_iff_printed
#print axioms AdalyFormal.RBridge.collar_power_ell2
#print axioms AdalyFormal.RBridge.collar_power_ell3
#print axioms AdalyFormal.RBridge.core8Applied_iff_print
#print axioms AdalyFormal.RBridge.headline_in_print_terms
#print axioms AdalyFormal.RBridge.headline_R_before_k
#print axioms AdalyFormal.RBridge.printed_nonvacuous
#print axioms AdalyFormal.RBridge.printed_discriminates

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
 [
  ``AdalyFormal.RBridge.admissible_iff_print,
  ``AdalyFormal.RBridge.blockClosed_iff_sum,
  ``AdalyFormal.RBridge.om0clause_iff_print,
  ``AdalyFormal.RBridge.collar_iff_rat,
  ``AdalyFormal.RBridge.om0Print_collar,
  ``AdalyFormal.RBridge.om0Print_least,
  ``AdalyFormal.RBridge.om0Print_char,
  ``AdalyFormal.RBridge.collar0_violated_of_not_sup,
  ``AdalyFormal.RBridge.om1_sub_om0Print,
  ``AdalyFormal.RBridge.om0All_collar_imp_eq,
  ``AdalyFormal.RBridge.om0Lt_collar_imp_eq,
  ``AdalyFormal.RBridge.om0Lt_eq_rad,
  ``AdalyFormal.RBridge.om0Print_sub_unit,
  ``AdalyFormal.RBridge.readings_differ,
  ``AdalyFormal.RBridge.alt_readings_violate_collar0,
  ``AdalyFormal.RBridge.cube5_class_box_printed,
  ``AdalyFormal.RBridge.collar_threshold_iff_printed,
  ``AdalyFormal.RBridge.collar_power_ell2,
  ``AdalyFormal.RBridge.collar_power_ell3,
  ``AdalyFormal.RBridge.core8Applied_iff_print,
  ``AdalyFormal.RBridge.headline_in_print_terms,
  ``AdalyFormal.RBridge.headline_R_before_k,
  ``AdalyFormal.RBridge.printed_nonvacuous,
  ``AdalyFormal.RBridge.printed_discriminates]

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
