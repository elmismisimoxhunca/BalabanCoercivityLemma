# Balaban’s Multiscale Coercivity Theorem in Lean 4

**A formal reconstruction of Balaban’s multiscale coercivity theorem and its supporting machinery for three-dimensional SU(2) lattice gauge theory, with an explicit audit of statement fidelity.**

The source is Tadeusz Balaban, *Propagators for lattice gauge theories in a background field*, Communications in Mathematical Physics **99** (1985), 389–434, especially the lower bound on p. 428. This is a component of Balaban’s renormalization-group programme for lattice Yang–Mills theory—not a proof of continuum Yang–Mills existence or the mass gap.

The development proves the coercivity estimate, constructs the required gauge/chart and multiscale right-inverse machinery, and tests which hypotheses and source conventions matter. It does **not** assume coercivity or the existence of the propagator inverses in its strongest theorem.

**Scope:** dimension 3, gauge group SU(2), compatible periodic lattices, and the explicitly defined regularity and coverage class. Lean **v4.31.0** and the mathlib revision are pinned in [`lean/`](lean/).

## Start here

- **Exact strongest statement and proof:** [`lean/src/TT_F.lean`](lean/src/TT_F.lean), `AdalyFormal.Total.P428Target8Total` and `AdalyFormal.Total.p428Target8Total`.
- **Original frozen headline:** [`lean/src/RI6.lean`](lean/src/RI6.lean), `AdalyFormal.M2RightInv.p428Target8 : AdalyFormal.StatementLaneG.P428Target8`.
- **What the hypotheses and conclusion mean:** [`lean/src/ZT5A.lean`](lean/src/ZT5A.lean), especially `InstIneq`, `InstAtWD`, and `CoercG8AtWD`.
- **Source comparison:** [statement sheet](notes/statement_sheet.pdf), [reference metadata](references/README.md), and the [research index](AHP/README.md). These are working documents, not a completed expert review. The draft `paper/` directory is not part of this release.
- **Reproduction:** [`REPRODUCE.sh`](REPRODUCE.sh), with instructions below.
- **Release scope and provenance:** [`RELEASE.md`](RELEASE.md).
- **Later research, including unsuccessful attempts:** [`AHP/README.md`](AHP/README.md). The archive is not covered wholesale by the core build.

## What the theorem says

In schematic notation, the conclusion is

\[
\gamma_0 E(\widetilde B) \leq \mathcal Q_U(C_U\widetilde B),
\]

where \(E\) is the formal bond energy, \(C_U\) is the propagator-based map, and \(\mathcal Q_U\) is the quadratic form. The exact operators, support conditions, and admissible-field constraints are in `InstIneq`; the displayed formula is an overview, not a replacement for that definition.

The important point is **uniformity**, not just positivity of one finite matrix. In `P428Target8Total`:

1. Choose a block factor \(\ell\geq2\) and \(a>0\).
2. The theorem supplies thresholds \(m_1\geq1\), \(R_1\), and positive constants \(a_0,\gamma_0\).
3. Those choices work for **every** cube factor \(c\geq10\), \(m\geq m_1\), \(R\geq R_1\), depth \(k\geq1\), and compatible torus, tower, domain, and background configuration satisfying the stated hypotheses and

\[
0<\alpha_0,\qquad c\ell^m\alpha_0\leq a_0.
\]

Both **inverse existence** (`WellDefG`) and **coercivity** are conclusions. The constants are chosen before \(c,m,R,k\), the torus, and the configuration. The theorem does not assert explicit or sharp numerical values for them.

## What is reconstructed

This is not a generic coercivity estimate with Balaban’s analytic ingredients left as assumptions. Among the proved ingredients are:

- **Local gauge/chart constructions:** the chart input used by the strongest theorem is proved in [`TT_Z.lean`](lean/src/TT_Z.lean).
- **A covariant right inverse for multilevel averaging:** [`RI5.lean`](lean/src/RI5.lean) proves `AdalyFormal.M2RightInv.classRightInvCov`, with weighted norm and covariant-gradient bounds. Its precise specification is [`OL15.lean`](lean/src/OL15.lean).
- **The multiscale assembly:** the local estimates and operator constructions feed the uniform coercivity theorem and its stronger parameter-order variants.
- **Nontrivial joint witnesses:** [`NVC7.lean`](lean/src/NVC7.lean), `AdalyFormal.NonVacC.headline_regime_nonvacuousC`, exhibits proper depth-two towers, nonzero curvature, configurations that are not pure gauge, nonempty domains, and nonzero admissible fields satisfying the hypotheses together. This is not a richness theorem at every depth.

The formal implication chain includes FamilyTorus / Family → Mixed → Total → the frozen headline. The declarations, module manifest, numbered Check files, and research reports record their individual scopes.

## Fidelity to Balaban’s statement

**Kernel correctness and fidelity to a printed theorem are separate questions.** Lean checks the encoded statements; it does not decide what an informal convention in the original paper was intended to mean.

The principal disclosed choices include:

- dimension 3 and SU(2), with periodic, aligned lattice geometry;
- explicit admissible towers, collars, and local per-cube gauge regularity;
- **site and common-plaquette coverage** by class cubes—an additional explicit hypothesis, not a clause printed in the cited lemma;
- interior-plaquette localization and specified bond, norm, and scaling conventions.

The project studies these choices mathematically rather than hiding them:

- The encoded coverage-free statement is refuted **even when inverse existence is granted**. This is a result about that formal class, not an unqualified assertion that Balaban’s theorem is false.
- Cube containment, exact collar bounds, and level-zero alternatives have positive and negative results, with family and parameter restrictions recorded in the statements and historical handoff.
- The **full-guard all-plaquette variant is proved**: [`SolR345Audit.full_guard_literal`](lean/src/SolR345Audit.lean).
- The weaker, **first-inverse-only all-plaquette formulation remains formally open**. Later exploratory numerics strongly disfavor it; that is not a formal counterexample and does not affect the proved main theorem.

[`HANDOFF.md`](HANDOFF.md) and the [research reports](AHP/README.md) record qualifications, review limits, and historical updates. Later entries can supersede older ones. Some historical references point to an unpublished `paper/` directory. The statement sheet is not automatically regenerated from later research; a stale “open” entry is not itself an up-to-date verdict.

## How to reproduce the checked core

Requirements: `git`, Python 3, [elan](https://github.com/leanprover/elan), access to the pinned Lean/mathlib downloads, roughly 25 GB of disk space, and at least 16 GB of RAM. A cold build of the 2,782 registered project modules can take several hours.

```sh
git clone https://github.com/elmismisimoxhunca/BalabanCoercivityLemma
cd BalabanCoercivityLemma
./REPRODUCE.sh
```

The script selects the pinned toolchain, obtains dependencies, builds the registered Lake libraries, runs the numbered `#print axioms` checks, validates complete records (including wrapped lists), compares their normalized output with [`expected/`](expected/), and checks the forbidden-token inventory. There are 572 main records and one separate historical R7 record. A successful run ends with:

```text
ALL CHECKS PASSED
```

For an existing compatible mathlib build, the offline dependency mode is:

```sh
PACKAGES_FROM=/path/to/compatible/.lake/packages ./REPRODUCE.sh
```

The reproduction script defaults to two concurrent Lean compiles. Its header documents memory and concurrency controls. **Release verification reuses the accepted snapshot’s build caches and local mathlib dependencies. It is a cache-assisted replay, not a fresh cold rebuild; the complete network-download path has not been validated end to end.**

The lightweight validator tests can be run separately:

```sh
python3 -m unittest discover -s tools/tests -v
```

### What the checks establish—and what they do not

- The checked main results have recorded axiom dependencies contained in `{propext, Classical.choice, Quot.sound}`. Proofs depending on `sorryAx` are not accepted.
- **The repository is not entirely `sorry`-free.** Five legacy modules contain placeholders in the import chain of a historical, superseded-statement result. The checked theorem dependencies do not use those placeholders. The explicit allowlist is [`expected/forbidden_tokens.expected.txt`](expected/forbidden_tokens.expected.txt); see `HANDOFF.md` for the distinction between imports and proof dependencies.
- [`tools/check_axioms.py`](tools/check_axioms.py) rejects unexpected axioms, truncated lists, malformed messages, and empty output. Earlier private reproduction scripts compared only first lines; the public release fixes that limitation and includes [regression tests](tools/tests/). Five historical expected lines were expanded from their retained complete records; no allowed axiom set was relaxed.
- The root reproduction command checks the registered core, **not every exploratory file or numerical script** in a research supplement. Builder-only compilation, independent replay, conditional implications, numerical evidence, and open premises must remain distinguishable.
- AI-assisted construction and model reviews are not independent human expert endorsement of source fidelity. Human mathematical review and better exposition remain valuable.

## Repository map

| Path | Purpose |
|---|---|
| [`lean/`](lean/) | Pinned Lake project; theorem sources and numbered axiom checks. |
| [`lean/MODULES.tsv`](lean/MODULES.tsv) | Module manifest, source hashes, and provenance. |
| [`lean/RENAMES.tsv`](lean/RENAMES.tsv) | Packaging renames for colliding historical modules. |
| [`expected/`](expected/) | Expected axiom-message output and explicit legacy-token allowlist. |
| [`notes/statement_sheet.pdf`](notes/statement_sheet.pdf) | Clause-by-clause comparison intended for statement review. |
| [`extras/two_domain/`](extras/two_domain/) | Supplemental two-domain work, **not part of the default build**. |
| [`AHP/`](AHP/README.md) | Later proofs, counterexample searches, numerics, reviews, and blueprints, with explicit evidence levels. |
| [`research/workflows/`](research/workflows/) | Historical AI-workflow definitions; inert process provenance, not installed automations. |
| [`references/`](references/README.md) | Bibliography and hashes of excluded third-party source material. |
| [`HANDOFF.md`](HANDOFF.md) | Detailed verification history, packaging exceptions, and remaining questions. |

## License and source materials

The project’s original material is licensed under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/); see [`LICENSE`](LICENSE). This does **not** grant redistribution rights to third-party papers, page images, or transcriptions held in a private working copy. They are not needed to execute the Lean build; consult the original publications for the source text.
