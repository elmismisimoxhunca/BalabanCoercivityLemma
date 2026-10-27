# Round 11 refutation track: certified window 0 < a ≤ 8

## Result

**GoalAllA is not closed.** The strongest compiled result here is
`Round11.Refute.window8_closed_proved` in `Attempt.lean`:

\[
\forall\ell\ge2,\quad 0<a\le8\ \Longrightarrow\
\neg\operatorname{P428TouchFourAt}(\ell,a).
\]

`not_touchFour_every_ell_le_eight` is the directly applicable theorem.
`window8_proved` and `not_touchFour_every_ell_eight` retain the open-window
spelling \(0<a<8\). This is an exact slice refutation, not a toy-matrix result:
the original scale, radius, smallness-cap and coercivity-constant quantifiers,
`ClassCoupledFour`, corner Delta, corner J, and `InstIneqS` are unchanged.
There is no parity restriction on ell.

The shared `../pin/Statement.lean` was created from the round-7 pin verbatim,
with `Round11.GoalAllA` and `Round11.GoalLargeA` appended, then compiled.
`Attempt.lean` contains that entire shared pin verbatim after two frozen imports.

## New argument

1. On every outward normal boundary bond, take the same nonzero SuTwo witness
   with transverse sign \((-1)^{y+z}\); all tangential bonds carry zero field.
   The background is still the frozen exterior-only path `Uth`.
2. `normal_delta` proves the full frozen plaquette calculation exactly:
   \(\langle A,\Delta(U_\pi)A\rangle=-8\langle A,A\rangle\).
   Each selected normal-transverse plaquette has central holonomy -1 and curl
   twice the signed normal field. The other plaquette direction contributes zero.
3. `normal_locality` decomposes this field into frozen normal singletons.
   Linearity gives \(WA=A\), \(TA=0\), touching support, and zero contribution
   to every higher-level Q row. `mass_le_of_high_zero` bounds the remaining
   level-zero rows by \(a\langle A,A\rangle\). It does **not** assert a global
   mass operator \(aI\).
4. `Fth_pi_bound_eight` therefore supplies a nonzero witness with
   \(\langle A,G^{-1}(\pi)A\rangle\le(a-8)\langle A,A\rangle\).
   The torus side is \(M\ell^2(6R+2)\), hence even for every ell, including odd ell.
5. For \(a<8\), frozen continuity, symmetry, PSD at zero and strict IVT give a
   singular point before pi. For \(a=8\), `exists_nonunit_path_le` also allows
   the endpoint: if the endpoint is PSD, the nonzero zero-quadratic-form witness
   is in its kernel (`psd_kernel`); otherwise strict IVT applies to a negative
   direction. Thus `exists_nonunit_eight_closed` gives a singular point in
   the closed interval from zero to pi.
6. The round-7 locality/class proofs are reused verbatim. In particular corner
   and all-plaquette compressed carriers agree, and `Uth` satisfies the touching
   class for every angle, including pi. The same NV geometry, positive-energy
   competitor and frozen totalized-inverse collapse finish the exact headline
   slice. No inverse guard is silently added.

## Exact remaining obstacle

The checkerboard-normal identity is **exactly -8**, not an unbounded negative
direction. For a>8 its proved carrier upper bound is positive, so neither the
strict nor endpoint IVT argument establishes singularity. `GoalAllA` and
`GoalLargeA` both remain unproved; there is no positivity claim for a>8.

The probe's rational three-component collar could extend the finite window to
152/17, but that mixed tangential/interior field is not formalized here. It needs
new Delta evaluation and collar locality beyond the frozen outward-normal
singleton lemmas used above. The probe's bounded-valence estimates are not
Lean-certified here and must not be promoted into a large-a headline proof.
An all-positive-mass refutation would need a mechanism beyond merely enlarging
this normal checkerboard direction.

## Verification

Only the mandated compiler driver was used for Lean compilation:

```sh
AHP/round3/lean1.sh AHP/round11/pin/Statement.lean
AHP/round3/lean1.sh AHP/round11/refute-r1/Attempt.lean
```

Both current `.exit` files contain 0. The final attempt log has no errors or
warnings. Every local definition and theorem has a `#print axioms`; all printed
sets are subsets of `{propext, Classical.choice, Quot.sound}`. `AUDIT.json`
records source hashes, verbatim-pin checks and the declaration/axiom audit.
There are no forbidden proof placeholders or foreign proof mechanisms.
Imports are only `D1Final`, `GdPlaq`, and `D1Lit` from frozen `lean/src`.

No numerical result is used as proof. No build, REPRODUCE script, git commit/push,
protected-source edit, or integration-checkout operation was performed.
Intermediate scratch Lean files were removed from this track directory.

Resource note: compilation used the shared two-slot driver, sequentially in
this track. An initial 8-GiB *virtual-address-space* cap prevented reading a
Mathlib olean; the completed compilations used the driver without that cap.
Peak RSS was not measured (`/usr/bin/time` is not installed); no measured
peak-memory compliance is claimed.
