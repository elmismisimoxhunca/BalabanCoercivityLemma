/-
Owned lemma file (compute/m1_si1_astra_match/lemma/). Imports the frozen `AdalyFormal` package
read-only (via its own default `LEAN_PATH` root `compute/forall_u_rung/deps`), plus a READ-ONLY
hash-verified copy of `ModifiedAverageDeriv.lean`/`.olean`, copied unedited into `lemma/deps/`
only for `LEAN_PATH` visibility (source hash `767f9f97…`, matching the live hash recorded in
`compute/m1_si1_astra_match/defs/DEFINITION_AUDIT.md` for "M" and in `ProdFullAssembleDerivNoLoop.lean`'s
own header; verified byte-identical against `compute/m1_si1_noloop/prod/deps/ModifiedAverageDeriv.{lean,olean}`
before this file was written). Neither the original nor the copy is edited.

## TARGET

`expand/CHANNEL_EXPANSION.md` §7, lemma **L1**, first clause: identify `UbarTowerCov.cPlusS 1 m c`
(the far endpoint used by the compiled `prod`/`outer` derivative, CMP98's `c₊` at stride 1) with
`ModifiedAverageDeriv.cPlus m c` (the far endpoint used inside the compiled modified average
`𝓜_V` itself). This is the *first*, hypothesis-free piece of L1's "Forward path carrier
dictionary": no coarse-block fitting, no cardinality hypothesis, no `CoarseBond L (ell*m)`
subtype cast is needed for THIS equality — those belong to L1's second/third clauses (the
`unitSitesOf`/`blockOf` identification and the `OneStep124.cPlus` subtype coercion), which are
NOT attempted here and remain unpaid.

Both sides unfold to the same `Nat.iterate (fun w => periodicLatticeShift w c.2) m c.1`:
`cPlusS s ell c := coarsePathEndpoint s c.1 (List.replicate ell c.2)`, and the paid
`coarsePathEndpoint_replicate` already identifies this with `pathSite c.1 c.2 (s*ell)`
(`cPlusS_eq` states that identification using `coarseShift`, which is `pathSite` under a swapped
argument order — the same `Nat.iterate`, so `rfl`-equal); `ModifiedAverageDeriv.cPlus ell c :=
pathSite c.1 c.2 ell` verbatim. So at `s = 1` only `Nat.one_mul` stands between them.
-/
import AdalyFormal.Balaban.UbarTowerCovariance
import ModifiedAverageDeriv

set_option autoImplicit false

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeEdge)

/-- **L1, first clause.** At stride `1`, the far endpoint `cPlusS` used by the compiled
`prod`/`outer` derivative agrees, ON THE NOSE, with the far endpoint `cPlus` used inside the
compiled modified average `𝓜_V`. No fitting/cardinality/subtype-cast hypothesis is needed. -/
theorem cPlusS_one_eq_modifiedAverageDeriv_cPlus {L : PeriodicLatticeExtent} (m : ℕ)
    (c : PeriodicLatticeEdge L) :
    AdalyFormal.Balaban.UbarTowerCov.cPlusS 1 m c = AdalySI1.ModifiedAverageDeriv.cPlus m c := by
  rw [AdalyFormal.Balaban.UbarTowerCov.cPlusS_eq, one_mul]
  rfl

#print axioms cPlusS_one_eq_modifiedAverageDeriv_cPlus
