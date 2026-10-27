import L0C2
import TT_F
import MX_F

/-!
# THL5 -- the base law (T6) of `Admissible` is not consumed by the proved headlines, except in two lemmas (lane thin_layer_20261019)

`ThinReplay.AdmT` is `Admissible` with the sixth clause (T6, the base law `Omega_0 = {M-blocks within R M of Omega_1}`) replaced by the tautology
`x ∈ Omega_0 ↔ x ∈ Omega_0`; i.e. the first five clauses (nesting, vanishing above `k`, divisibility, block-closure, strict collars at radius `R`).
The `run_cmd` at the end REPLAYS every declaration `D` in the dependency closure of the proved headlines that mentions `Admissible`, directly or through another member of `D`,
into the kernel with `Admissible` replaced by `AdmT` (and every inlined copy of the T6 clause replaced by the tautology), under the names `ThinScan.<original name>`.
Each replayed declaration is type-checked by the kernel when it is added.  All but two typecheck verbatim; the two that do not are the declarations that CONSUME or PRODUCE the
T6 clause: `AdalyFormal.Thin.admissible_lift` (transport of `Admissible` along a thin-torus cover) and `AdalyFormal.L0C.path_exists` (path lemma of the cap lane).  For these two
the replay inserts the re-proofs `admissible_lift_T` / `path_exists_T` below (T6 is not needed: the cap lemma uses the strict level-0 collar instead).  Any other failure aborts the
build (`throwError`).  The structures with an `Admissible` field (`CTData`, `CTBase`, `LocHyp`) are replayed as inductive types.
The mirrored headlines (e.g. `ThinScan.UNI.Total.p428Target8FamilyTorusU`) are the proved headlines for towers satisfying only T1-T5.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 8000

open Lean Elab Command
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

namespace ThinReplay

/-- `Admissible` without the base law: the first five clauses, at radius `R`; the sixth is the tautology. -/
def AdmT {L : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j : ℕ, k < j → S.Om j = ∅) ∧
  (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j : ℕ, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ j : ℕ, j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j →
      ∀ y ∈ S.Om (j + 1), R * bigSide M ell j < pdist x y) ∧
  (∀ x : PeriodicLatticeSite L, x ∈ S.Om 0 ↔ x ∈ S.Om 0)

end ThinReplay

namespace AdalyFormal.Thin

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open ThinReplay (AdmT)

/-- re-proof of `AdalyFormal.Thin.admissible_lift` for `AdmT` (no base-law clause to transport). -/
theorem admissible_lift_T {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell M R k : ℕ} {S : Tower L}
    (hS : AdmT ell M R k S) : AdmT ell M R k (liftTower h S) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hS
  refine ⟨fun j x hx => h1 j hx, fun j hj => ?_, fun j hj μ => (h3 j hj μ).trans (h μ), fun j hj => ?_, fun j hj x hx y hy => ?_,
    fun x => Iff.rfl⟩
  · ext x; exact ⟨fun hx => by have := h2 j hj; rw [Set.eq_empty_iff_forall_notMem] at this; exact (this _ hx).elim, fun hx => hx.elim⟩
  · exact blockClosed_lift h _ (fun μ => h3 j hj μ) _ (h4 j hj)
  · have := h5 j hj (projS h x) hx (projS h y) hy
    exact lt_of_lt_of_le this (pdist_proj_le h x y)

end AdalyFormal.Thin

namespace AdalyFormal.L0C

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open ThinReplay (AdmT)

variable {L : PeriodicLatticeExtent}

/-- re-proof of `AdalyFormal.L0C.path_exists` for `AdmT`: the strict level-0 collar replaces the base law. -/
theorem path_exists_T {ell M R k : ℕ} {S : Tower L} (hA : AdmT ell M R k S) (hMR : 1 ≤ R * M)
    {z : PeriodicLatticeSite L} {s : ℕ} {x₀ : PeriodicLatticeSite L} (hx₀ : x₀ ∈ siteBox z s) (hx₀1 : x₀ ∈ S.Om 1) :
    ∀ n : ℕ, ∀ y : PeriodicLatticeSite L, y ∈ siteBox z s → bd z x₀ y = n → y ∉ S.Om 1 →
      ∃ u ∈ siteBox z s, u ∈ S.Om 0 ∧ u ∉ S.Om 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy hn hy1
    have hne : y ≠ x₀ := fun h => hy1 (h ▸ hx₀1)
    obtain ⟨y', hy'b, hpd, hlt⟩ := exists_step hx₀ hy hne
    by_cases h1 : y' ∈ S.Om 1
    · refine ⟨y, hy, ?_, hy1⟩
      by_contra hnot
      have hc := hA.2.2.2.2.1 0 (Nat.zero_le _) y hnot y' h1
      have hb : bigSide M ell 0 = M := by simp [bigSide]
      rw [hb] at hc
      omega
    · exact ih (bd z x₀ y') (by omega) y' hy'b rfl h1

end AdalyFormal.L0C

namespace ThinReplay

def admName : Name := `AdalyFormal.StatementLane.Admissible
def admNew : Name := `ThinReplay.AdmT

def usedConsts (ci : ConstantInfo) : Array Name :=
  let a := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => a ++ d.value.getUsedConstants
  | .thmInfo d => a ++ d.value.getUsedConstants
  | .opaqueInfo d => a ++ d.value.getUsedConstants
  | _ => a

partial def reach (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        for m in usedConsts ci do
          if !seen.contains m then stack := m :: stack
        match ci with
        | .inductInfo iv => for c in iv.ctors do if !seen.contains c then stack := c :: stack
        | _ => pure ()
  return seen

def mapName (n : Name) : Name := `ThinScan ++ n

/-- the inlined T6 clause: `∀ x : PeriodicLatticeSite L, x ∈ Om0 ↔ ∃ ... pdist ...`; replaced by `∀ x, A ↔ A`. -/
def t6repl (e : Expr) : Option Expr :=
  match e with
  | .forallE n ty body bi =>
    match ty.getAppFn.constName?, body with
    | some c, .app (.app (.const ``Iff _) a) b =>
      if c.getString! == "PeriodicLatticeSite" && b.getUsedConstants.any (fun m => m.getString! == "pdist") then
        some (.forallE n ty (mkApp2 (.const ``Iff []) a a) bi)
      else none
    | _, _ => none
  | _ => none

partial def substE (D : NameSet) (e : Expr) : Expr :=
  e.replace fun e => match e with
    | .const c ls => if c == admName then some (.const admNew ls) else if D.contains c then some (.const (mapName c) ls) else none
    | .proj s i b => if D.contains s then some (.proj (mapName s) i (substE D b)) else none
    | _ => t6repl e

end ThinReplay



open ThinReplay in
set_option Elab.async false in
run_cmd do
  let env ← getEnv
  let roots := [`UNI.Total.p428Target8FamilyTorusU, `MXQ.Total.p428Target8FamilyTorus, `AdalyFormal.Total.p428Target8Total,
                `MXP.Total.p428Target8Mixed, `AdalyFormal.L0C.cap_unconditional, `AdalyFormal.M2RightInv.p428Target8,
                `AdalyFormal.M1.perCube_of_M1]
  let patches : List (Name × Name) :=
    [(`AdalyFormal.Thin.admissible_lift, `AdalyFormal.Thin.admissible_lift_T), (`AdalyFormal.L0C.path_exists, `AdalyFormal.L0C.path_exists_T)]
  for r in roots do
    if (env.find? r).isNone then throwError "THL5: missing root {r}"
  for (o, p) in patches do
    if (env.find? o).isNone || (env.find? p).isNone then throwError "THL5: missing patch pair {o} {p}"
  let R := reach env roots
  let names := R.toList
  let mut D : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for n in names do
      if D.contains n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        if (usedConsts ci).any (fun m => m == admName || D.contains m) then
          D := D.insert n; changed := true
    -- inductive rule: a member constructor drags its inductive type, its constructors and recursor in
    for n in D.toList do
      match env.find? n with
      | some (.ctorInfo cv) =>
        if !D.contains cv.induct then D := D.insert cv.induct; changed := true
        match env.find? cv.induct with
        | some (.inductInfo iv) =>
          for c in iv.ctors do if !D.contains c then D := D.insert c; changed := true
          let r := cv.induct ++ `rec
          if !D.contains r then D := D.insert r; changed := true
        | _ => pure ()
      | _ => pure ()
  -- dependencies for ordering
  let depsOf (n : Name) : Array Name :=
    match env.find? n with
    | none => #[]
    | some (.ctorInfo cv) => #[cv.induct]
    | some (.recInfo rv) => #[rv.getMajorInduct]
    | some (.inductInfo iv) =>
      iv.ctors.foldl (fun acc c => match env.find? c with
        | some ci => acc ++ ci.type.getUsedConstants.filter (fun m => D.contains m && m != n && !iv.ctors.contains m)
        | none => acc) (iv.type.getUsedConstants.filter (fun m => D.contains m))
    | some ci => (usedConsts ci).filter D.contains
  let mut order : Array Name := #[]
  let mut visited : NameSet := {}
  for n in D.toList do
    if visited.contains n then continue
    let mut stack : List (Name × Bool) := [(n, false)]
    while true do
      match stack with
      | [] => break
      | (m, done) :: rest =>
        stack := rest
        if done then
          order := order.push m
        else
          if visited.contains m then continue
          visited := visited.insert m
          stack := (m, true) :: stack
          for c in depsOf m do
            if !visited.contains c then stack := (c, false) :: stack
  IO.println s!"THL5 replay: |D| = {D.size}, ordered {order.size}"
  let mut nok := 0; let mut npatched := 0; let mut nskip := 0; let mut nind := 0
  let mut failed : Array Name := #[]
  for n in order do
    match env.find? n with
    | none => pure ()
    | some ci =>
      let nn := mapName n
      let ty := substE D ci.type
      match patches.find? (fun p => p.1 == n) with
      | some (_, pn) =>
        match ci with
        | .thmInfo d =>
          let pv : Expr := mkConst pn (d.levelParams.map mkLevelParam)
          liftCoreM <| addDecl (.thmDecl { name := nn, levelParams := d.levelParams, type := ty, value := pv })
          npatched := npatched + 1
        | _ => throwError "THL5: patched declaration {n} is not a theorem"
      | none =>
      match ci with
      | .ctorInfo _ => nskip := nskip + 1
      | .recInfo _ => nskip := nskip + 1
      | .inductInfo iv =>
        if iv.all.length != 1 then
          failed := failed.push n
        else
          let ctors := iv.ctors.map fun c => { name := mapName c, type := substE D ((env.find? c).get!).type : Constructor }
          try
            liftCoreM <| addDecl (.inductDecl iv.levelParams iv.numParams [{ name := nn, type := ty, ctors := ctors }] iv.isUnsafe)
            nind := nind + 1
          catch _ => failed := failed.push n
      | .thmInfo d =>
        try
          liftCoreM <| addDecl (.thmDecl { name := nn, levelParams := d.levelParams, type := ty, value := substE D d.value })
          nok := nok + 1
        catch _ => failed := failed.push n
      | .defnInfo d =>
        try
          let dv : Expr := substE D d.value
          liftCoreM <| addDecl (.defnDecl { name := nn, levelParams := d.levelParams, type := ty, value := dv, hints := d.hints, safety := d.safety, all := [nn] })
          nok := nok + 1
        catch _ => failed := failed.push n
      | _ => failed := failed.push n
  IO.println s!"THL5 replay: replayed {nok} theorems/definitions, {nind} inductives, {npatched} patched, {nskip} ctor/rec skipped, {failed.size} FAILED"
  for n in failed do IO.println s!"THL5 FAILED {n}"
  if !failed.isEmpty then throwError "THL5: replay failed for {failed.size} declarations"
  for n in D.toList do
    match env.find? n with
    | some (.recInfo _) =>
      if !(← getEnv).contains (mapName n) then throwError "THL5: missing replayed recursor {n}"
    | _ => pure ()

-- the mirrored headlines, with their axioms
#print axioms ThinScan.UNI.Total.p428Target8FamilyTorusU
#print axioms ThinScan.MXQ.Total.p428Target8FamilyTorus
#print axioms ThinScan.AdalyFormal.Total.p428Target8Total
#print axioms ThinScan.MXP.Total.p428Target8Mixed
#print axioms ThinScan.AdalyFormal.L0C.cap_unconditional
#print axioms ThinScan.AdalyFormal.M2RightInv.p428Target8
#print axioms ThinScan.AdalyFormal.M1.perCube_of_M1
#print axioms AdalyFormal.Thin.admissible_lift_T
#print axioms AdalyFormal.L0C.path_exists_T
