# Balaban’s Multiscale Coercivity Theorem in Lean 4

A formalisation of Balaban’s multiscale coercivity theorem and its supporting constructions for **three-dimensional SU(2) lattice gauge theory**.

The theorem is a key estimate in Balaban’s renormalization-group programme. It gives a positive lower bound for a propagator-based quadratic form, uniformly over the number of renormalization levels and the background configurations in the specified regularity class. The development includes the local gauge charts, a covariant right inverse for multilevel averaging, and the estimates needed to assemble the bound.

**Source:** Tadeusz Balaban, *Propagators for lattice gauge theories in a background field*, Communications in Mathematical Physics **99** (1985), 389–434, especially p. 428.

## Main result

The strongest theorem is [`AdalyFormal.Total.p428Target8Total`](lean/src/TT_F.lean). In schematic notation, its lower bound is

\[
\gamma_0 E(\widetilde B) \leq \mathcal Q_U(C_U\widetilde B),
\]

where \(E\) is the bond energy and \(C_U\) and \(\mathcal Q_U\) are the propagator-based map and quadratic form. Their exact definitions and the admissible-field conditions are given by [`InstIneq`](lean/src/ZT5A.lean).

For each \(\ell\geq2\) and \(a>0\), the theorem chooses thresholds \(m_1,R_1\) and positive constants \(a_0,\gamma_0\). These work for every cube factor \(c\geq10\), \(m\geq m_1\), \(R\geq R_1\), and depth \(k\geq1\), subject to the geometric and regularity hypotheses and

\[
0<\alpha_0,\qquad c\ell^m\alpha_0\leq a_0.
\]

Thus the constants are chosen **before** the cube factor, scales, depth, torus, and background configuration. Both **existence of the required inverses and coercivity are proved**, rather than assumed.

The supporting constructions include:

- [Local gauge charts](lean/src/TT_Z.lean).
- [A covariant multilevel right inverse](lean/src/RI5.lean), with weighted norm and covariant-gradient bounds.
- [Nontrivial admissible examples](lean/src/NVC7.lean): depth-two towers with nonzero curvature, a background that is not pure gauge, and a nonzero admissible field.

See [Results and scope](RESULTS.md) for the theorem map and the statement-fidelity results.

## Scope and relation to the source

The formalisation uses compatible periodic, aligned lattices, explicit tower and collar conditions, and local per-cube gauge regularity. Its class includes **site and common-plaquette coverage**, an explicit additional hypothesis not printed in the cited lemma, and its operators use interior-plaquette localization.

These choices are examined in separate theorems. In particular, the encoded coverage-free statement is refuted even when inverse existence is granted. Alternative touching conventions, normalizations, and guarded all-plaquette formulations are also studied. The [statement sheet](notes/statement_sheet.pdf) provides a clause-by-clause source comparison; [Results and scope](RESULTS.md) gives the current mathematical status.

This is a formal reconstruction of Balaban’s coercivity theorem under stated conventions—not a claim of literal equivalence under every reading of the source, or a proof of continuum Yang–Mills existence or the mass gap.

## Check the proofs

Requires `git`, Python 3, and [elan](https://github.com/leanprover/elan). Lean **v4.31.0** and mathlib are pinned. Allow roughly 25 GB of disk space, at least 16 GB of RAM, and several hours for a cold build.

```sh
git clone https://github.com/elmismisimoxhunca/BalabanCoercivityLemma
cd BalabanCoercivityLemma
./REPRODUCE.sh
```

A successful run ends with `ALL CHECKS PASSED`. The script builds the registered Lean modules, checks complete axiom-dependency records, and compares them with the expected results. The checked theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

Five legacy modules contain unused `sorry` declarations; the checked theorem dependencies do not use them. See [Verification](verification/README.md) for the exact evidence, build options, and limitations.

## Navigate the repository

| Path | Content |
|---|---|
| [`lean/src/`](lean/src/) | Formal definitions and proofs. Start with `TT_F.lean`, `ZT5A.lean`, and `RI6.lean`. |
| [`lean/MODULES.tsv`](lean/MODULES.tsv) | Module index and source hashes. |
| [`lean/src/AHP/`](lean/src/AHP/) | Statement-fidelity results included in the main build. |
| [`verification/`](verification/README.md) | Build evidence and complete axiom records. |
| [`AHP/`](AHP/README.md) | Supplemental proofs, numerical experiments, and blueprints; not all included in the main build. |
| [`references/`](references/README.md) | Bibliography and source-page references. |

## License

[CC BY-SA 4.0](LICENSE).
