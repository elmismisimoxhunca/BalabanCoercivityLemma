# Guarded exact-kernel route — round 5, kernel pass 2

**closedGoal: `none`. No actual separating lattice instance was constructed.**

Final file: `AHP/round5/guarded/kernel-r2/Attempt.lean`.

**This exact final path has a fresh successful wrapper compilation**, unlike the interrupted combined draft from pass 1. The main new partial declaration is

`AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation` (`Attempt.lean:2608`).

It is an **explicitly conditional reconstruction on the actual lattice carrier**, not an existence theorem for lattice modes, an exterior configuration, or a counterexample. Both negative pinned goals remain open. Its realization premise is not proved.

## 1. What was recovered and verified first

`Inherited.lean` is a byte-for-byte copy of `kernel-r1/KernelDraft.lean`. It includes:

- the entire round-3 pin, unchanged;
- the full round-4 refute-r1 attempt, unchanged;
- both repaired exact two-coordinate models from pass 1;
- the previously unverified full-vector kernel/unit and cofinal lifting draft.

The inherited file was compiled **before adding the new Schur work**, through:

```sh
AHP/round3/lean1.sh AHP/round5/guarded/kernel-r2/Inherited.lean
```

Exit **0**, no warnings/errors. All 157 local declarations have dependency records; all 176 records, including inherited extra prints, use only the permitted dependencies. Thus the prior draft's conditional results are now verified, not merely printed during a failed file compilation:

- `KernelR1.two_mode_unit` and `two_mode_kernel`;
- `KernelR1.actual_two_mode_separation` (`:2326`);
- `KernelR1.mode_requires_positive_source_pairing` (`:2349`);
- `KernelR1.dil_class_exterior_independent`;
- `KernelR1.cofinalPencilFailure_of_dil_modes` and `goalNeg2_of_dil_modes`.

These results **retain their mode-realization hypotheses**. Compiling them does not construct a realization. The inherited matrix diagnostics are still matrices, not lattice instances. No earlier round was edited or had its verification evidence overwritten.

## 2. New unconditional lattice result: exterior tuning freezes the localized data

`dil_local_data_exterior_independent` (`:2442`) proves equality of the **entire actual localized base data** for

\[
U=\operatorname{dilU}(q,R,\varepsilon,V),\qquad
U'=\operatorname{dilU}(q,R,\varepsilon,V').
\]

Hypotheses retained: \(q>0\), even \(R\), and the room condition \(34\le R(2q)\). The interior parameter \(\varepsilon\), mass parameter \(a\), tower and region are fixed; the exterior fields \(V,V'\) are arbitrary.

The proof uses frozen `StatementLaneR8.data_congr` and the exact agreement of `dilU` on every both-endpoint interior bond. This is not a claim of locality of an inverse in its input.

`dil_bulk_correction_exterior_independent` (`:2459`) extracts

\[
B(U')=B(U),\qquad D(U')=D(U),
\]

where \(B=G^{-1}_{\rm in}\) and \(D\) is the **assembled genuine localized correction**, with its actual source, constrained solution and second jet. This holds for the curved family, not just the known flat-interior path.

Consequently, changing exterior links alone cannot turn a zero localized correction into a nonzero correction, or create a missing positive localized source pairing. Those properties must already be established for the fixed curved interior. This theorem does **not** prove that the family's correction is zero or nonzero.

## 3. New exact Schur-complement reconstruction

### Why the literal two-mode lift is restrictive

The inherited ansatz requires full-vector identities

\[
Bu=u+tv,\quad Bv=tu+(1+d)v,\quad Du=0,\quad Dv=dv,
\]
\[
\Theta u=(t^2-1)u,\quad\Theta v=0,
\]

and injectivity on the remaining orthogonal complement. It yields the kernel \(u-tv\), but requires an invariant two-dimensional subspace, not just two entries of a compression. In particular it forces \(DBu=tdv\ne0\). Long-distance transmission through eliminated lattice modes need not have that one-step form.

The new work permits those eliminated components instead of dropping them.

### Exact blocks, with all inverses accounted for

Let \(E\) be the actual full carrier, and suppose a continuous linear equivalence is supplied:

\[
e:E\simeq\mathbb R^2\times\mathbb R^n.
\]

For an actual operator \(T:E\to E\), `corner11/12/21/22` are the four exact blocks of \(eTe^{-1}\). Define

\[
S_T=T_{11}-T_{12}T_{22}^{-1}T_{21},\qquad
L_Tx=e^{-1}\bigl(x,-T_{22}^{-1}T_{21}x\bigr).
\]

`liftKernel_image` (`:2513`) proves, **assuming `IsUnit T22`**,

\[
e(TL_Tx)=(S_Tx,0).
\]

`liftKernel_ne_zero` and `liftKernel_mem_kernel` give an exact full-carrier nonzero kernel when \(x\ne0\) and \(S_Tx=0\). `unit_of_schur_unit` (`:2544`) proves that units of **both** \(T_{22}\) and \(S_T\) imply a unit of the full \(T\).

No inverse/compression interchange occurs. The inverse in the formula is explicitly the inverse of the complementary block, and its unit is a hypothesis, never inferred from the full guard.

### Specialization to the genuine lattice pencil

Write

\[
A=(\mathrm{dataS}_{\rm all}).Ginv,\qquad
D=(\mathrm{dataS}_{\rm in}).Delta2,\qquad F=A-D.
\]

`actual_schur_separation` assumes \(t,d\ne0\), units of \(A_{22}\) and \(F_{22}\), and the **exact effective-block identities**

\[
S_A=\begin{pmatrix}t^2&t\\t&1+d\end{pmatrix},\qquad
S_F=\begin{pmatrix}t^2&t\\t&1\end{pmatrix}.
\]

It then proves a full-carrier unit of \(A\), since \(\det S_A=t^2d\ne0\), together with the explicit nonzero full-carrier kernel

\[
z=L_F(1,-t)
=e^{-1}\left((1,-t),-F_{22}^{-1}F_{21}(1,-t)\right),
\qquad Fz=0.
\]

This is a genuine reconstruction theorem for the pinned operators, **conditional on a dictionary and exact block calculations that have not been supplied for any lattice instance**. The two coordinates remain an abstract effective plane. They have not been identified with particular bond fields, Fourier sectors, or gauge modes.

The complement need not be invariant under the original operator. This is the difference from the previous full-vector ansatz. No equivalence between the new realization obligation and a negative pinned goal is asserted.

## 4. Cofinal class obligations remain correctly wired

`SchurRealisation` (`:2635`) records the above unproved block realization for the actual assembly. `DilSchurRealisation` (`:2654`) requires it along the existing curved family, with one fixed \(a>0\), every positive \(q\), every even \(R\ge6\), and every \(0<\varepsilon<1\), choosing an exterior field afterward.

`cofinalPencilFailure_of_dil_schur` (`:2663`) and `goalNeg2_of_dil_schur` (`:2691`) are compiled **conditional** implications. They use the copied refute-r1 family, not a surrogate class. The witnesses are still

\[
m=m_0+1,\quad q=2^{m_0},\quad R=2(R_0+18),\quad k=1.
\]

The radius is chosen **before** the positive cap. The cap-dependent interior parameters come from `dil_in_class_nonflat_competitor`. The previously compiled fixed-parameter exterior class transfer justifies choosing \(V\) after those parameters. All torus, admissibility, `LambdaOK2`, coverage, regularity, capped-smallness, and positive-energy competitor obligations are retained.

`DilSchurRealisation` is not proved. These implications therefore do not close `GoalNeg2` or `GoalNeg1`.

## 5. Precise remaining obstacle

No exterior field \(V\), no physical two-coordinate dictionary \(e\), and no exact block evaluation realizing the separation have been found, even at one admissible instance. In particular:

1. **Actual nonlinear correction visibility is unproved.** Interior holonomy does not imply nonzero \(D\). The literal positive-eigenvalue ansatz would require
   \[
   \langle H_{\rm in}C^{(2)}_{\rm in}(v),J_{\rm in}\rangle=d/2>0
   \]
   for a normalized mode. The inherited conditional positivity theorem is now compiled, but this pairing has not been evaluated positively for the curved family. Exterior tuning cannot change it at fixed interior parameters, by the new locality theorem.
2. **Compression is insufficient.** In an actual split the corrected effective operator is
   \[
   S_F=(A_{11}-D_{11})-(A_{12}-D_{12})(A_{22}-D_{22})^{-1}(A_{21}-D_{21}).
   \]
   It is not obtained by subtracting just the visible two-by-two correction from \(S_A\). The eliminated contributions and both complementary units must be certified. No such full calculation is present.
3. **A full-carrier unit is essential.** A nonsingular selected sector alone leaves the other sectors unchecked. The new theorem makes this obligation explicit rather than pretending the selected matrix's determinant proves the guard.
4. **Cofinality is spectral as well as geometric.** The existing family handles the nonspectral quantifiers, but does not preserve spectral separation under dilation. The missing construction must work with fixed \(a\), cofinal \(m,R\), and arbitrary subsequent caps. A single finite matrix sample or cap-dependent radius would not suffice.

The available localized estimates do not forbid such a construction, but neither supply it. The flat-interior crossing has \(D=0\) and cannot be substituted. No numerical eigenvalue or finite-difference correction was used as a zero certificate. No numerical script was run.

## 6. Final verification and hygiene

The final command was:

```sh
AHP/round3/lean1.sh AHP/round5/guarded/kernel-r2/Attempt.lean
python3 AHP/round5/guarded/kernel-r2/audit.py
```

The final wrapper exit is **0**, at the actual final path, without warnings or errors. Two earlier completed exit-1 runs exposed only proof elaboration issues in the new Schur appendix; these were repaired before the final successful run. No compilation timed out in this pass, and no duplicate interrupted process was relaunched.

Main record:

```text
'AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All **179 local declarations** have individually matched fully qualified dependency records. All **198 dependency records**, including inherited frozen-root prints, use only the permitted three dependencies. There are **22 new declarations** beyond the now-verified inherited draft. `audit.py` checks the exact complete pin prefix, unchanged inherited/refute prefixes, sole frozen import `DrEquiv`, absence of forbidden source constructs, actual source/log/exit order, final-path exit zero, absence of diagnostics, and full dependency-print coverage.

Final source SHA-256:

```text
600d01a0b80ae6e6eeb7d4a9d991c7cd24a637f614c8f7ea7e9259d9c8a165f7
```

The requested judgement and PIN, route notes/obstacle text, mining report, inherited draft/models, and relevant frozen data-locality/operator definitions were inspected. The large mining catalogue was paged through the read tool; it was not independently re-proved. All statement-fidelity qualifications of the pin remain in force. No source-reading conclusion about the unqualified printed lemma is claimed.

All authored files are under `AHP/round5/guarded/kernel-r2/`. The temporary appendix assembly fragment was removed after exact final assembly and successful compilation were checked. No protected source, earlier AHP round, lakefile, paper, notes, expected output or extras was edited. No terminal, direct compiler/Lake command, reproduction, dependency update, numerical sweep, commit or push was used. No deletion outside this attempt directory occurred.
