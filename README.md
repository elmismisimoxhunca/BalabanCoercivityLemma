# Multiscale coercivity for SU(2) lattice gauge theory

A Lean 4 formalisation of Balaban’s multiscale coercivity estimate in three dimensions, together with local gauge constructions, multilevel averaging, and comparisons of boundary and regularity assumptions.

**Reference:** Tadeusz Balaban, *Propagators for lattice gauge theories in a background field*, Communications in Mathematical Physics **99** (1985), 389–434. The coercivity estimate appears on p. 428.

## Coercivity estimate

For an admissible background configuration \(U\) and field \(\widetilde B\), the estimate has the schematic form

\[
\gamma_0 E(\widetilde B)\leq\mathcal Q_U(C_U\widetilde B),
\]

where \(E\) is the bond energy, \(C_U\) is a propagator-based map, and \(\mathcal Q_U\) is a quadratic form.

For each block factor \(\ell\geq2\) and \(a>0\), there are thresholds \(m_1,R_1\) and constants \(a_0,\gamma_0>0\) such that the required inverses exist and the estimate holds for every \(c\geq10\), \(m\geq m_1\), \(R\geq R_1\), and depth \(k\geq1\), subject to the geometric and regularity assumptions and

\[
0<\alpha_0,\qquad c\ell^m\alpha_0\leq a_0.
\]

The constants are independent of the subsequently chosen cube factor, scales, depth, torus, and background configuration. The supporting results include local gauge charts and a covariant right inverse for multilevel averaging, with weighted norm and gradient bounds.

## Assumptions and scope

The setting consists of compatible periodic lattices, aligned blocks, admissible towers and collars, and local per-cube gauge regularity. Site coverage and common-plaquette coverage are explicit assumptions; these are additional conditions not printed in the cited lemma. The operators use interior-plaquette localization.

Depth-two examples satisfy these assumptions with nonzero curvature, a background that is not pure gauge, and a nonzero admissible field. Separate comparisons examine coverage, touching conventions, normalization, and all-plaquette formulations.

The conclusions concern these specified conventions. They do not assert equivalence with every interpretation of the original text, continuum Yang–Mills existence, or a mass gap.

[Mathematical results](RESULTS.md) · [References](references/README.md)

## Verification

Requires `git`, Python 3, and [elan](https://github.com/leanprover/elan). Lean v4.31.0 and the mathlib revision are pinned. A cold build requires roughly 25 GB of disk space, at least 16 GB of RAM, and several hours.

```sh
git clone https://github.com/elmismisimoxhunca/BalabanCoercivityLemma
cd BalabanCoercivityLemma
./REPRODUCE.sh
```

The command checks compilation and axiom dependencies. Success ends with `ALL CHECKS PASSED`. The checked theorem dependencies are contained in `{propext, Classical.choice, Quot.sound}`.

[Verification details](verification/README.md) · [Formal definitions and proofs](lean/src/)

## License

[CC BY-SA 4.0](LICENSE).
