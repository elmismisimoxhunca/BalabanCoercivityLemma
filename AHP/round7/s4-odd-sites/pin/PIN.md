# S-4 — odd-scale sites-only coercivity

## Status and exact targets

**Pinned and compiled; analytic status OPEN.** No `Goal1`–`Goal4` is proved or refuted here. Compilation of a proposition definition is not proof of that proposition.

`Statement.lean` uses the actual body `CovAssume.FamilyTorusSitesConstAt` from `lean/src/CaT2d.lean:122`. Its local copy is verbatim, in namespace `AdalyFormal.Round7.S4OddSites`; `body_eq_frozen` proves equality by `rfl`. Its only imports, `SoA3` and `SoPar`, are frozen modules from `lean/src`. No AHP import, substituted operator, or unproved placeholder is used.

| Goal | Plain words |
|---|---|
| `Goal1` | For **every odd blocking factor \(\ell\ge3\)**, every natural cube factor \(c\ge10\), and every real \(a>0\), the sites-only constant-family body holds. |
| `Goal2` | For **each** such \((c,\ell,a)\), that body is false. No divisibility or width premise is added. |
| `Goal3` | The positive assertion for fixed **\(\ell=13\)**, still every \(c\ge10\), \(a>0\). |
| `Goal4` | The negative assertion for fixed **\(\ell=13\)**, still every \(c\ge10\), \(a>0\). |

Goals 3/4 are fallback targets within the recorded odd-\(L>11\) range. Goal1 implies Goal3; Goal2 implies Goal4; both opposing pairs are incompatible. These facts compile. **Goal2 is stronger than the exact negation of Goal1**, and similarly Goal4 versus Goal3: the all-parameter assertions can both fail if different parameter triples have different answers. No excluded-middle argument decides this table.

### Quantifiers and guard

For fixed \(c,\ell,a\), the body is

\[
\exists m_1\ge1\;\exists R_1\;\exists a_0>0\;\exists\gamma_0>0\;
\forall m\ge m_1\;\forall R\ge R_1\;\forall k\ge1\;\forall L_u\;\forall\alpha_0>0\;\cdots.
\]

The remaining premises are exactly:

- \(M=\ell^m\), \(\eta=\ell^{-k}\), and \(cM\alpha_0\le a_0\);
- `TorusOK`, `Admissible`, and `LambdaOK2`;
- **`CovSitesF ∧ PerCubeRegularF`** for `constFam c`;
- the antecedent **`GenP.WellDefG`** contained in `InstIneqWDH`.

The conclusion is the frozen inequality for **every** admissible independent field, with the actual `genC`, `genForm`, and `bondEnergy`. Plaquette coverage is absent. Inverse existence is **assumed**, not concluded. `WellDefG` includes bijective `H0`, units of `G1inv` and `Nmat`, and the padded site inverse, `Ginv`, and `Q G Q*` unit guards (`ZT4A`, `ZXG3A`). This is not the separate Ginv-only all-plaquette guarded question.

Thus a singular carrier, a failed guard, a negative unconstrained Hessian direction, a scalar chain crossing, or a finite numerical sample cannot by itself refute this body. A refutation must defeat every proposed threshold/positive-constant tuple with actual guarded, sites-covered data. The cofinal class result below chooses scale and radius before receiving the positive cap, but supplies no violating field.

## Relationship to the even results

`CaT2d.not_familyTorusSitesConstAt_two` settles only \(\ell=2\), for every \(c\ge10,a>0\). `SoA1`/`SoA2` extend failure to an even arithmetic window, requiring evenness explicitly. Their analytic entry point `SoM3.main_neg_S` has the binder `2 ∣ ell`.

A proof of Goal2, combined with the existing \(\ell=2\) theorem, would extend failure to **all odd scales**, with no arithmetic restriction on the factor. Goal4 would already extend it to the source-range scale 13 for every allowed factor. Neither negative target is a re-export of the even theorem. The positive goals would instead establish a parity distinction; they do not logically strengthen the existing negative theorem.

The existing `chain_instance_S` is valid at odd scales under its remaining hypotheses, but does not prove the actual guarded full-form result. The old fixed-magnitude integer-step obstruction rules out only one cancellation mechanism, not odd-scale failure generally.

## Departures and retained readings relative to Balaban's print

This pin changes **only the scale range** of the already-defined sites-only family question. It does not claim to re-identify that formal question with the unqualified printed lemma. Inherited conventions and differences are:

1. **Dimension/group:** finite three-dimensional SU(2), not an arbitrary dimension/group result.
2. **Geometry:** rectangular periodic tori, extent fields counting side minus one, periodic \(\ell^1\) distance, and explicit side divisibility/room (`TorusOK`). Periodicity, tiling hygiene and padding are formal conventions.
3. **Scale and tower:** \(\eta=\ell^{-k}\), aligned half-open big blocks of \(M\ell^j\) fine sites; nested, block-closed domains with strict fine-lattice collars and empty padding above \(k\). The p.396 base is the exact union of M-blocks within RM of \(\Omega_1\), using reading A of \(T_1\). The permitted p.394 thinner-layer and two-domain readings are not substituted.
4. **Lambda:** frozen unit-lattice M/ell-block closure, top-domain containment, touching support and strict collar using the same R as the tower. Empty Lambda is allowed. The source identification of the common radius remains a reading.
5. **Class cubes:** aligned product boxes and unique index in two adjacent strata; a single common factor c, rather than arbitrary per-cube O(1) factors or general block unions. Here c ranges over all naturals at least 10, not just 12. The p.408 third-enlargement condition is not added.
6. **Coverage:** site coverage is an added formal hypothesis not explicitly printed. Plaquette coverage is deliberately dropped. This question is not about deleting all coverage or adopting a corner-coverage repair.
7. **Bonds and regularity:** `CubeBond` requires both endpoints, not the printed touching convention. Gauges and Hermitian traceless logarithm fields are chosen separately per cube. Forward differences are guarded by both sampled bonds and curl-of-curl by the entire sampled stencil; the encoded curl form replaces the printed derivative expression. Full Frobenius class bounds retain the disclosed square-root-of-two normalization difference.
8. **Selectors and boundary operators:** Delta/J use fully inside plaquettes (`plaqIn`), with the frozen touching-bond carrier and Dirichlet construction. Neither all-plaquette nor one-corner operators are used. The S-1 boundary dictionary is not settled by this pin.
9. **Averaging/jets:** retain the genuine frozen componentwise one-step and iterated averaging jets, weights, adjoints, multi-level constraints, and construction of the nonlinear correction. No new identification with the printed averaging formulas is claimed.
10. **Independent variables:** retain `OnLambdaTildeIn`, `OnLambdaT`, the staircase/dropped-bond convention, touching Lambda support, and the coupled corridor solve defining `genC`. This is not a new proof of equivalence to the print's local single-variable prescription.
11. **Form and units:** retain eta and top-level tau-star insertion in the first term, mass subtraction, nonlinear J term, and trace-normalized Hilbert–Schmidt bond energy. Round-2/3/5 S-3 comparisons supply qualified normalization evidence under their dictionaries/guards; this track does not repeat or broaden them. The CMP109 supplement for the nonlinear remainder remains disclosed.
12. **Inverse domain:** all operators still use the frozen totalization internally, but this particular inequality is required only under `WellDefG`. It neither requires an inequality at failed guards nor asserts inverse existence throughout the sites-only class. It does not decide an unguarded or Ginv-only guarded variant.
13. **Parameter range/order:** all positive a, k at least one, and arbitrary natural R above a threshold. M is a power of ell, while R is not restricted to powers as on p.408. The constant-family body fixes m1, R1, a0 and gamma0 **before both m and R**, stronger uniformity than the basic frozen headline's displayed order and beyond the print's explicit independence of k and U. They may depend on c, ell and a. Smallness is `c M alpha0 ≤ a0`, not an explicit numerical threshold. No separate `SidePow6` conjunct is appended to the copied body.
14. **Odd convention:** Goals 1/2 include 3, 5, 7, 9, 11 as well as odd values greater than 11; Goals 3/4 use 13. The CMP109 p.251 quotation is used as recorded in OPEN_ITEMS S-4, not newly image-verified. Whether it is a standing convention governing the earlier CMP99 assertion remains reading-only. No even counterexample is silently transported to odd L.

Neither the arithmetic subfamily used below nor its fixed depth two is a restriction of the pinned goals. A negative result only for \(c=9\ell+1\), for example, would be useful but would **not** settle Goal2 or Goal4.

## Both-direction attempt and furthest compiled partial result

See `../attempt/Partial.lean` and `../attempt/ATTEMPT.md`.

- **Toward proof:** the direct implication from sites to plaquettes is false even cofinally in the scale and radius. `no_eventual_geometric_upgrade` proves this at \(c=9\ell+1\) for every \(\ell\ge3\). The existing both-coverage theorem cannot settle the sites-only question merely by taking larger thresholds. An analytic or guard-sensitive argument is not excluded.
- **Toward refutation:** use the period-ell profile \(1,-1,\ldots,1,-1,0\). `oddProfile_block_sum` proves exact zero integer sums on every aligned ell-square at every odd ell. `oddProfile_not_const_step` proves that no one fixed natural step magnitude describes it. This explicitly escapes the old parity obstruction rather than asserting that obstruction is wrong.
- `sliceCfg_class` proves actual per-cube regularity for **any** Cartan phases on the hidden slice. `oddCfg_cofinal_class` assembles actual torus compatibility, admissibility, Lambda, site coverage, failed plaquette coverage and all-positive-cap regularity for the new profile, at arbitrarily large m and R, with factor \(9\ell+1\) and thin width 19. At ell=13 this factor is 118.
- `sliceCfg_holonomy_01` / `oddCfg_holCos_01` give actual plaquette holonomy/weight formulas. `oddCfg_zero_wellDefG` proves the full frozen guard at the flat parameter zero, including at odd scales. It says nothing about the guard at a nonzero crossing.

**Remaining obstacle:** the variable steps create different transverse plaquette weights, so the uniform-weight Z-chain argument cannot simply be reused. Integer sums have not been lifted to the actual principal-log blocked-background and jet identities. Nonzero-parameter inverse certificates, the coupled/perpendicular-sector analysis, a genuine admissible positive-energy competitor with a violating full form, and an all-factor cofinal construction remain missing. Conversely, there is no class-wide coercivity estimate for guarded sites-covered but plaquette-uncovered backgrounds. All four analytic goals remain open.

## Verification boundary

Compile only with:

```
AHP/round3/lean1.sh AHP/round7/s4-odd-sites/pin/Statement.lean
AHP/round3/lean1.sh AHP/round7/s4-odd-sites/attempt/Partial.lean
```

Successful wrapper `.lean.exit`/`.lean.log` files sit beside both sources. Every retained printed dependency list is a subset of `propext`, `Classical.choice`, `Quot.sound`. Fresh byte-identical replay evidence and hashes are recorded in `../VERIFY.md` / `../VERIFY.json`; this is builder replay, not an independent reviewer or whole-project rebuild. No headline proof is inferred from these checks. No numerical experiment was used. Protected sources, earlier rounds, paper and statement sheet were not edited, and no commit/push was made.
