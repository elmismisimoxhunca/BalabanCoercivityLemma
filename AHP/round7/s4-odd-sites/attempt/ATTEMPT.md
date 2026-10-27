# Two-sided attempt: open, with compiled variable-step family

All four goals in `../pin/Statement.lean` remain open. No positive or negative analytic headline has been proved. The current `Partial.lean` and its byte-identical replay both compile with exit 0, no diagnostics, and only permitted dependencies. Namespace: `AdalyFormal.Round7.S4OddSites.Partial`.

## Negative direction: escape the old parity obstruction

For odd ell, define the period-ell integer profile

\[
h_\ell=(1,-1,\ldots,1,-1,0),\qquad
U(x,0)=\operatorname{cartan}(t\,h_\ell(x_1))\quad\text{at }x_0=C,
\]

with U identity on other bonds. This is `oddProfile` and `oddCfg`, not a substitute matrix model.

Compiled:

- `oddProfile_periodic`, `oddProfile_aligned`: exact ell-periodicity and aligned translation.
- `oddProfile_sum`, `oddProfile_block_sum`: every aligned ell-square has zero integer sum for every odd ell. The profile is independent of the second transverse coordinate.
- `oddProfile_first_step`, `oddProfile_seam_step`, `oddProfile_not_const_step`: the first difference is -2 and the wrap difference is 1; no fixed natural magnitude describes all steps. Thus the old constant-step obstruction does not apply. This does not contradict the obstruction theorem.
- `sliceCfg_class`: **arbitrary real Cartan phases** on the hidden direction-0 slice are per-cube regular at every positive alpha0 under the existing `SoRel` geometry. No small-angle bound is needed for this class assertion, because each class cube misses all changed bonds.
- `sliceCfg_holonomy_01`, `oddCfg_holCos_01`: actual (0,1)-plaquette holonomy and cosine weight are given by the neighboring profile difference, using the actual periodic shift. These are operator-input identities, not spectral conclusions.
- `oddCfg_cofinal_class`: with thin width 19 and factor \(c=9\ell+1\), for arbitrary proposed m1/R1 there are m/R above them with the genuine torus, admissible tower, Lambda, site coverage, failed plaquette coverage, and positive capped per-cube regularity for every t. Radius and scale are chosen before the cap. This theorem applies to every ell at least 3; the mean-zero profile theorem additionally needs oddness.
- `oddCfg_zero_wellDefG`: the full frozen guard holds at **t=0** for positive a, ell at least 2, positive M divisible by ell, and R at least 1. It combines the actual flat H0 bijectivity, four flat units, and padded-site unit. This is a guard witness, not proof of an open interval of nonzero guarded parameters.

Representative retained records:

```
'AdalyFormal.Round7.S4OddSites.Partial.oddProfile_block_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round7.S4OddSites.Partial.oddCfg_cofinal_class' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round7.S4OddSites.Partial.oddCfg_zero_wellDefG' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Missing negative step

The sums are arithmetic, not a theorem about principal-log branches or `stridedBlockedGauge`. The actual profile introduces two step magnitudes and hence different weights; one cannot insert a single cosine into `chain_instance_S` and reuse `main_neg_S`.

Needed next: derive the actual blocked-background and linear/second-jet identities for this profile, analyze the period-ell transverse coupled sectors (not merely a one-dimensional compression), establish all `WellDefG` conditions at a suitable **nonzero** parameter, and construct a nonzero admissible competitor for which the full `genForm (genC ...)` defeats the proposed bound. Cofinality of geometry/regularity does not give cofinality of the spectral violation. Extending from the factor \(9\ell+1\) to every c is another obstacle to Goals 2/4. No numerical experiment or claimed crossing was used.

## Positive direction: the geometric shortcut is ruled out

The positive both-coverage theorem remains available, but site coverage cannot be upgraded to plaquette coverage just by increasing thresholds. `EventualCoverageUpgrade` spells out that proposed geometric route with genuine TorusOK and Admissible hypotheses. `no_eventual_geometric_upgrade` refutes it at \(c=9\ell+1\), for every ell at least 3, by the cofinal class geometry above.

```
'AdalyFormal.Round7.S4OddSites.Partial.no_eventual_geometric_upgrade' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This excludes only the geometric implication. It does not exclude a rule using the inverse guard, a different analytic proof, or positivity of the actual sites-only body. The zero-parameter guard shows guarded configurations do exist on the candidate geometry, but no general coercivity estimate on the extra configurations has been proved.

## What counts and what does not

The furthest compiled result is an actual cofinal sites-covered/per-cube-regular variable-profile family, its exact plaquette inputs, a flat full-guard witness, and a geometric proof-route obstruction. It is not `FamilyTorusSitesConstAt`, its negation, or a conditional theorem with a hidden claimed spectral realization. No headline closure is reported.

The pin imports only frozen modules; this independent partial file likewise imports only `SoA3` and `SoPar`. It uses no AHP imports or parent-state changes. The `verify/` copies are fresh serial **builder replays**, not an independent judge. See `../VERIFY.md` and the machine-readable audit for exact hashes, counts and boundaries.
