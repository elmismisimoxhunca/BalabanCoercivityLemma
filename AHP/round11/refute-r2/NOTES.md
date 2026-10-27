# Round 11 refute-r2: certified window through 4√5

## Result

**GoalAllA remains open; `closedGoal` is `none`.** The strongest compiled result is
`Round11.RefuteR2.window_sqrt5_closed_proved` in `Attempt.lean`:

\[
\forall\ell\ge2,\qquad 0<a\le4\sqrt5
\quad\Longrightarrow\quad
\neg\operatorname{P428TouchFourAt}(\ell,a).
\]

The upper endpoint is included. Numerically it is approximately 8.94427191,
strictly improving round 1's endpoint 8. The directly usable theorem is
`not_touchFour_every_ell_le_sqrt5`. The rational corollary
`not_touchFour_every_ell_le_rational` covers \(0<a\le152/17\).
No restriction to even ell, no inverse guard, and no replacement of the original
scale/radius/cap/coercivity quantifiers is introduced.

## New proof

The checkerboard amplitude `f` remains supported on outward boundary sites.
The new field is

\[
 A(x,0)=n f(x)+m f(x+e_0),\qquad
 A(x,1)=A(x,2)=t f(x).
\]

`mixedField` therefore includes the boundary normal, the immediately inward
normal, and the two boundary tangentials. This is the right-boundary convention;
`t` has the opposite sign from the probe's left-boundary coordinates.

The following statements concern the **actual frozen lattice operators**:

1. `collar_locality` generalizes the singleton locality argument: if every
   nonzero bond starts within distance two of the complement and
   \(17\ell\le RM\), then \(WA=A\), \(TA=0\), and every higher-level Q row
   vanishes on A. `mixed_locality` verifies this hypothesis and touching support.
   The reused `mass_le_of_high_zero` consequently bounds the actual weighted
   mass by \(a\langle A,A\rangle\); no global mass-equals-aI identity is asserted.
2. `mixed_inner` proves
   \[
   \langle A,A\rangle=(n^2+m^2+2t^2)\sum_x\langle f(x),f(x)\rangle.
   \]
3. `mixed_delta_le` evaluates/bounds the complete frozen plaquette sum at pi:
   \[
   \langle A,\Delta(U_\pi)A\rangle
   \le[-8n^2+8m^2+8(n+m)t]\sum_x\langle f(x),f(x)\rangle.
   \]
   All pi-background transports are trivial in the adjoint representation,
   and every holonomy is central. The outward face contributes a negative
   curl square. The inward face is bounded above by its positive curl square;
   transverse curls vanish. Thus only an upper bound is needed, without an
   additional interior-thickness hypothesis.
4. Set \(n=1\), \(m=9-4\sqrt5=(\sqrt5-2)^2\), and \(t=2-\sqrt5\).
   `radical_identity` proves the coefficient identity, and `mixed_nonzero`
   establishes that the witness is nonzero. `Fth_pi_bound_sqrt5` gives
   \[
   \langle v,F(\pi)v\rangle\le(a-4\sqrt5)\langle v,v\rangle.
   \]
5. `exists_nonunit_sqrt5` reuses frozen continuity/symmetry/PSD-at-zero and the
   round-1 nonpositive-endpoint IVT lemma. Endpoint singularity is allowed,
   which retains \(a=4\sqrt5\).
6. The previous corner/all-selector transfer, touching-class membership,
   admissible NV slabs, positive-energy competitor, and totalized-inverse
   collapse are reused. They establish the exact pinned slice, not merely
   a three-by-three matrix assertion. The NV transverse period is even for
   every ell, including odd ell.

## Exact remaining gap

For \(a>4\sqrt5\), the proved endpoint bound is positive and supplies no
nonpositive witness for the IVT. Wider collars near 8.947 remain numerical
probe evidence, not a theorem here. No all-positive-mass singularity mechanism
or independent failure of the mass-subtracted final form has been established.
Neither `GoalAllA` nor `GoalLargeA` is proved, and no positivity claim for larger
mass is made. Bounded-valence observations from the probe are not promoted to
formal impossibility or large-mass-headline theorems.

## Verification and artifacts

- The pre-existing `../pin/Statement.lean` was left untouched. Its recorded
  compiler exit is 0; its round-7 prefix and complete verbatim inclusion in
  this attempt are checked by `audit.py`.
- Final compilation was run directly with the mandated two-slot driver:
  `AHP/round3/lean1.sh AHP/round11/refute-r2/Attempt.lean`.
  The final `.exit` is 0, and `.log` has no errors or warnings.
- All **59** local declarations have corresponding `#print axioms` output.
  Every dependency set is a subset of
  `{propext, Classical.choice, Quot.sound}`. The main output is:
  `'Round11.RefuteR2.window_sqrt5_closed_proved' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `audit.py` passes and writes `AUDIT.json`: source/pin/log hashes, complete
  declaration-to-axiom mapping, import checks, forbidden-token check, and
  fresh-log/exit checks. Run with
  `PYTHONDONTWRITEBYTECODE=1 python3 AHP/round11/refute-r2/audit.py`.
- Imports are only frozen `D1Final`, `GdPlaq`, and `D1Lit`. Unused round-1
  proof blocks were removed before the final successful compilation.
- No numerical inference is used as proof. This track wrote only under
  `AHP/round11/refute-r2/`; no build, REPRODUCE, protected edit, integration
  checkout operation, git commit/push, or deletion was performed.
- Compilation was sequential through the shared at-most-two-job driver.
  Peak RSS was not measured; no measured memory figure is claimed.
