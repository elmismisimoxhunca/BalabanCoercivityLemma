# Mining the frozen coercivity/inverse chain for the guarded all-plaquette question

**Task: declaration mining only. Guarded verdict: still open; no new theorem or counterexample.**

Read in full: `AHP/round3/guarded/JUDGEMENT.md`, `AHP/round3/guarded/pin/PIN.md`, and `AHP/round2/guarded/JUDGEMENT.md`. `Attempt.lean` is the complete round-3 pin copied byte-for-byte, with no appended proof and no goal changes. The search concerns the pinned formal reading, not a new reading of the printed papers.

## 1. Answer in brief

There is substantial compiled analysis to reuse, **but its class-uniform coercivity is for the localized assembly**. There is no result in the mined chain supplying the missing class-wide implication from invertibility of the all-plaquette carrier to invertibility of the corrected all-plaquette carrier.

1. **(a) Lower bounds:** `w4_classU` and the patch/IMS chain give weighted lower bounds for localized `P.data.Ginv`; `G1inv_coercive_strat` subtracts the localized correction bound. The `Total` proof chooses a positive constant `c1` depending only on \(\ell,a\), before the instance, and proves `hcoer` on the thick, localized configuration. The ordinary carrier-norm constant obtained from this weighted bound contains \(\ell^{-2k}\). Do not call that a positive depth-independent ordinary-norm spectral gap. `Total`'s final \(\gamma_0\) bounds the **pulled-back final form**, not `Ginv_all`.
2. **(b) Inverses:** `Total`, `Mixed`, and `FamilyTorus` really export `WellDefG` throughout their eventual classes, not just under a guard. This includes units of localized `Ginv`, `G1inv`, both relevant constraint covariances, the masked site operator, and bijectivity of `H0`. The old `RI6.p428Target8` exports the inequality, not `WellDefG` in its statement; `WellDefAt_loc_of_inst` extracts localized covariance-layer units from that inequality when a positive-energy admissible competitor exists.
3. **(c) Small correction:** the class bound for `Delta2` is linear in \(t=12M\alpha_0\), with constants from weighted columns of **localized** `H`, the raw second-jet bound, and `Wop`. The raw second jet is uniformly bounded under a smallness window; it is **not asserted to vanish linearly in \(\alpha_0\)**. It is quadratic in its **test input**, not an asserted quadratic function of the background. Here \(D\) is the assembled symmetric correction, not the raw jet. Smallness of the correction comes through the source pairing; no \(O(\alpha_0^2)\) claim is justified by these statements. The source estimate has an explicit uncovered-stencil term; it is not a fictitious all-bond bulk bound.
4. **(d) Locality:** there are exact background-congruence statements, finite read-balls for raw jets, support for right-inverse building blocks, and weighted exponential column bounds for localized `H` and `H1in`. None says that the full carrier inverses preserve the selector shell, or that \(B^{-1}\operatorname{range}\Theta\) lies in the raw-jet nullspace. Congruence when changing the background outside the base domain is not finite propagation in the **input** of an inverse.

The strongest usable bridge to `selAll` is conditional: `DrRed1.Delta2_lit_eq_loc` identifies its correction with localized `Delta2` when the all-plaquette carrier is a unit and localized `WellDefAt` holds. `Ginv_eq_on_V` compares the two carriers only on fields zero on every level-zero bond. The equality on `V0` is the available bridge for reusing localized estimates on that subspace; it does not give a bound on the complementary boundary directions. In the existing reductions \(\operatorname{range}\Theta\subseteq V_0^\perp\). Neither bridge controls the remaining boundary response or its inverse.

## 2. Proof spine and selector dictionary

The requested line `TT_F.lean:29` is the **definition** `P428Target8Total`. Its proved declaration is `AdalyFormal.Total.p428Target8Total` at **`lean/src/TT_F.lean:43`**.

```text
TT_F.p428Target8Total
  TT_C.strong_coreTC
    TT_C.strong_coreT
      TT_F.fieldsT              (argument supplied by TT_F, abstract in the core)
        TT_Z.ballChartsGT_proved
        TT_B.fieldsKT_of_ball
        TT_B.classRightInvCovT -> RI5.rightInv_cfg
        TT_B.classRightInvT_of_cov
        TT_B.opLayerThickT_of
      AU_SK3.w4_classU -> AC_MR4.patchCoercive_class_existsAC
                          -> MR2.patchCoercive_charts_exists
                          -> MI22.ginv_weighted_coercive
      MA13.cw_uniform + MA18.cwW4_lower
      UMC.dlayer_explicit -> AC_MZ5.dlayerStrat_classAC
      MI21.units_strat + TL22a.guardsUnit_of_fields
      AU_SK5.config_inst_classU
      ZR8Data.WellDefG_congr       (undo background localization)
      Thin.coverHyp_of_wd + AC_SV1.wellDefG_of_coverHyp
                                    (descend from a thick covering torus)
```

The `Mixed` (`MXP`) and `Family` (`MXQ`) cores are parallel generalizations of this chain, not alternative all-plaquette assemblies. `MXQ_Tor.p428Target8FamilyTorus` instantiates the family theorem at `embedFam F`. `MXQ_Br.P428Target8Family.toMixed` and `MX_F.P428Target8Mixed.toTotal` go back to the coarser class formulations.

The guarded equivalence follows a separate, older route:

```text
DrEquiv.P428Target8SG_iff_pencilT
  GdR5a.P428Target8SG_iff_residualT
  DrEquiv.residualT_iff_pencilT
    DrEquiv.GShape_imp
      RI6.p428Target8 -> localized inequality
      GdGen8.WellDefAt_loc_of_inst -> localized units (positive competitor)
    DrRed1.isUnit_G1inv_lit_iff_pencil
```

`RI6` is not the direct proof invoked by `TT_F.p428Target8Total`; it is a related earlier proof used by the guarded reduction. The machine trace distinguishes these roots rather than equating import reachability with proof dependency.

**Selector dictionary.** Unadorned `gparams(...).data`, `.G1inv`, `.H1in`, `GenP.genForm`, `InstIneq`, `InstAtWD`, `CoercG8AtWD` are frozen localized objects. `D1Literal.pin_target8` / `pin_target8_iff` (`D1Lit.lean:134–135`) identify their headline with `P428Target8S selIn selIn`; `pin_genForm` (`:138`) pins the form. Changing cube factors/families does **not** change `plaqIn` to `Set.univ`. Raw `C2fullOf` and `Wop` are common ingredients, not a proof that the resulting inverse products agree for all sources.

## 3. Constants: which choices actually precede which data?

### 3.1 Total, Mixed, FamilyTorus

`Total.P428Target8Total` (`TT_F.lean:29`):

\[
\forall\ell\ge2\ \forall a>0\ \exists m_1\ge1\ \exists R_1\ \exists a_0>0\ \exists\gamma_0>0\quad
\forall c\ge10\ \forall m\ge m_1\ \forall R\ge R_1\ \forall k\ge1,\mathrm{Lu},\alpha_0>0.
\]

Under \(c\ell^m\alpha_0\le a_0\), torus, tower, region and class hypotheses, the result is `CoercG8AtWD`. Every displayed constant precedes \(c,m,R,k,\mathrm{Lu},\alpha_0,S,\Lambda,U\). `strong_coreTC` states its equivalent existential block as \(\gamma_0,m_0,R_0,a_0\); reordering this existential-only block does not introduce a dependence on later universal instance data.

`MXP.Total.P428Target8Mixed` (`MX_F.lean:39`) puts the admitted factor set \(\Phi\) and its `CubeFactorSet` after that same constant block, before \(m,R,k,\mathrm{Lu},\alpha_0\), with the cap required for every admitted factor. `MXQ.Total.P428Target8Family` similarly chooses constants before its all-torus family `Fm`. `P428Target8FamilyTorus` (`MXQ_Tor.lean:58`) allows the **single-torus** family `F` even after \(m,R,k,\mathrm{Lu},\alpha_0\). It still concludes localized `InstAtWD`. The family's per-member coverage and both-endpoint regularity do not cover all plaquettes in an exterior shell.

### 3.2 The choices *inside* `strong_coreT`

Source: `TT_C.lean:51–100`, with instance coercivity at `:246–253`, units at `:266–278`, localization/descent at `:287–314`.

For fixed \(\ell,a\):

1. `w4_classU` chooses \(c_W,a_{0P},D\); `w4Num_exists` chooses \(W_0,\varepsilon_1,a_1\).
2. `cw_uniform` chooses \(\delta,c_1>0\), using \(\min(a,c_W/2)\). Set \(\Gamma=\texttt{Gam0}\ \ell\), \(T_1=4/(1-\varepsilon_1)+1\).
3. `eps_choice` chooses \(\varepsilon_J,\varepsilon_{2s}>0\), in particular \(\varepsilon_{2s}<c_1\); the other numeric windows, \(M_1\), and \(M_{c0}\) follow.
4. `FieldsKT` supplies \(d_f,m_F,R_F,K,C,s_F\), with \(1\le C\le K\). `OpLayerThickT` supplies \(m_O,R_O,\theta,K_H,K_{H1},K_2,C_W,K_D,s_O\). `ClassRightInvT` supplies \(m_Q,b_N,R_Q,s_Q\). `classSmall_exists` supplies \(\theta_c\).
5. Set \(d=\max(D,d_f)\), the explicit `a1D` below, and the minimum `sthr` of the stated numeric windows. The source defines

\[
a_{0,\mathrm{old}}=\min\!\left(\min\!\left(\min(s_F,\min(s_O,s_Q)),\min(a_{0P},\min(1,a_{1D}))\right),\frac{\mathrm{sthr}}{2\ell^3}\right),
\qquad a_0=\min(a_{0,\mathrm{old}}/K,\theta_c).
\]

6. Choose \(\gamma_0=\Gamma/(4T_1)\),
\[
m_0=m_F+m_O+m_Q+8+(d+64\ell^2+2)+M_1+(M_{c0}+1),
\]
\[
R_0=R_F+R_O+R_Q+W_0+9\ell+24+(\lceil1/\delta\rceil_++1).
\]
Only **then** are `fc,m,R,k,Lu,alpha0,S,Lam,U` introduced. On a thick configuration localized outside class bonds, the W4/D-layer pipeline uses \(\beta=K\alpha_0\). `strong_coreTC` converts an original-factor class to the hybrid factor-12 bounds using \(\alpha'_0=\mathrm{fc}\,\alpha_0/12\); constants stay before `fc`.

The local `have hcoer` is a fact within the compiled proof, **not a separately exported declaration**. The appendix therefore lists `strong_coreT`, `w4_classU`, and the precise supporting declarations, not a nonexistent `Total.hcoer` theorem. Likewise the final descent exports units and the final form; no separate globally quantified ordinary-norm carrier gap is claimed here.

### 3.3 Right inverses and operator layer

`TT_A.ClassRightInvCovT` / `TT_B.classRightInvCovT`: \(\ell,a\) first, then \(m_1,c_W,c_G,R_1,s\) with \(c_W,c_G\ge0\) and \(s>0\), then `fc,m,R,k,Lu,alpha0,...`, then each source \(u\), then a preimage \(x\) with `Q x = u`, weighted norm and covariant-gradient bounds. This is a right inverse of **Q**, not `Ginv_all`.

`ClassRightInvT` / `classRightInvT_of_cov`: \(\ell,a\), then \(m_1,b_N>0,R_1,s>0\), then instances, then \(v\), then a preimage \(g\) whose localized `Ginv` energy is **bounded above** by \(b_N\|\sqrt{\mathrm{massW}}\,v\|^2\). An upper-energy extension estimate is not a carrier coercivity lower bound. Both shapes initially require a thick torus and a background equal to identity off class bonds; the core later removes those auxiliary restrictions.

`OpLayerThickT` chooses its six constants and cap before all `fc,m,R,k,...`. `opLayerThickT_of` (`TT_B.lean:461`) obtains \(c_1,b_N\), a `DQSmall` window \(\beta_0\), and `num_ballB` constants before selecting \(\theta=\delta/2\). It fixes
\[
K_H=C_{HB}\sqrt{a\ell},\quad K_{H1}=C_{H1B}\sqrt{a\ell},\quad
K_2=44217\,\texttt{K2strat}(\ell,\beta_0),\quad C_W=\ell^2 C_{Wb},\quad K_D=2187\,\texttt{KDfree}\ \ell.
\]
The cap is then shrunk, including bounds forcing the conjugated correction constants \(\delta_0,\delta_1\) below the fixed numeric window. Its five fields are weighted `H` columns, weighted `H1in` columns, the raw `C2fullOf` bound, weighted `Wop`, and the unit second-jet bound. These are **not** operator-norm bounds for \(K_B^{-1}\).

## 4. Useful estimates and their precise limits

### (a) Weighted carrier and corrected carrier lower bounds

The main public nodes are `M2Route.patchCoercive_charts[_exists]` (`MR2`), `patchCoercive_class_existsAC` (`AC_MR4:26`), `M1IMS.ginv_weighted_coercive_of` (`MI2:185`), `ginv_weighted_coercive` (`MI22:172`), `M2Skel.w4_classU` (`AU_SK3:31`), and `M1Assembly.cwW4_lower` (`MA18:50`). Earlier `MI28`, `MI33`, and `MI34` variants are included separately, retaining their global-regularity/localization hypotheses rather than relabeling them as unconditional class theorems.

Writing \(w(A)=\texttt{wnormSq}\ S\ \ell\ k\ A\), the exact conclusions of the reusable subtraction lemmas are
\[
(c_w-\varepsilon_2)w(A)\le\langle A,G_{1,\mathrm{in}}^{-1}A\rangle,
\qquad
(c_w-\varepsilon_2)\ell^{-2k}\|A\|^2\le\langle A,G_{1,\mathrm{in}}^{-1}A\rangle.
\]
`MI21:51,68` **assume** the W4 and D-layer estimates; `MI21:86` additionally assumes injectivity of `Qs` and \(\varepsilon_2<c_w\), then concludes the two units. `R2Algebra.BaseDataS.G1inv_coercive` is the analogous generic norm-level conditional lemma. Generic `DLR1.coercive_inv_bound` can turn an available positive ordinary-norm lower bound into an inverse bound. It cannot manufacture a lower bound for the all-plaquette carrier from `IsUnit` alone.

Conjugated-energy/Combes–Thomas lower bounds and their hypotheses are also catalogued (`DC2`, `DG2b`, `DH1`, `DY4a`, `DY4b`, `OL7`). Their assumed localized positive energy is essential; no indefinite all-plaquette version is inferred.

### (b) What `WellDefG` actually says

`ZXG3A.lean:43` defines

```lean
Function.Bijective (H0 P.Lam P.Q1) ∧ IsUnit P.G1inv ∧ IsUnit (GenP.Nmat P)
```

as `GenP.WellDef`. `ZT4A.lean:46` defines `GuardsUnit` as

```lean
IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)) ∧
IsUnit P.data.Ginv ∧ IsUnit ((P.data.Q.comp P.data.G).comp P.data.Qs)
```

and `:51` defines `WellDefG := WellDef P ∧ GuardsUnit P`. The appendix includes the verbatim definitions and generalized compiled types.

`R2Algebra.exists_G1inv` only constructs the symmetric operator with the required quadratic form; **it does not assert its invertibility**. `Ring.inverse` remains totalized elsewhere. Do not mistake existence of this operator, a definition of an inverse, a `#check`, or a dependency print of a proposition definition for a proof of a unit or a proof of the open goal.

### (c) Actual small-field estimates

Let \(t=12M\alpha_0\). `AC_MZ3.Jf_splitAC` (`:37`, plus original/Mixed/Family versions) gives the source bound
\[
\|J_f(b)\|\le400\ell^3t\,\omega_J(b)+
\mathbf1_{\mathrm{Unc}}(b)\,4(2t+6t^2+1024t^3)\,\omega_U(b).
\]
The uncovered term is retained in `omSAC`. With the class column estimate and \(4t\le1\), `AC_OL8.psi_classAC` bounds
\[
\|\psi_D(p)\|\le\sqrt{\texttt{Ageo}(\ell,\theta)}K_H\,400\ell^3t.
\]
`AC_OL8.delta2_classAC` gives the full conjugated bilinear bound with coefficient
\[
2\bigl(\sqrt{\texttt{Ageo}(\ell,\theta)}K_H\,400\ell^3t\bigr)K_2e^{2\Omega}
\,44217(\ell k_W)^2,
\]
multiplying the two `wq` norms. Its class, room, column, raw-jet, conjugated-`Wop`, and oscillation premises are all present in its exact statement below.

`OL2.hC2_class` (`:297`) bounds \(\sum_p\|C_2(z)_p\|\) by `44217 * K2strat ell (...) * wnormSq z`; `DQ5.dqSmall_exists` and `K2strat_mono` freeze this coefficient before the instance. The `D2`/`C2` single-step and composite estimates are listed too. They bound a quadratic map in its input, not a linear operator small in the background parameter.

`DS1.delta2_strat` gives the useful un-conjugated bound
\[
|\langle A,\Delta^{(2)}A\rangle|\le2S_\psi K_2C_Ww(A).
\]
`AC_MZ5.dlayerStrat_classAC` also bounds the `H1in D2in`/source summand. `UMC.dlayer_explicit` (`:45`) chooses, **after the two tolerances and the fixed operator-layer constants but before depth/torus/background**,
\[
a_{1D}=\min\left(\frac14,
\min\left(\frac{\varepsilon_{2s}}{2\sqrt{\texttt{Ageo}}K_H\,400\ell^3K_2C_W+1},
\frac{\varepsilon_J}{\sqrt{\texttt{Ageo}}K_{H1}\,400\ell^3K_D+1}\right)\right).
\]
For \(12M\alpha_0\le a_{1D}\) it proves `DLayerStrat` under `OpLayer`; `Total.fieldsT` discharges that layer on its auxiliary thick/localized regime. All class variants in the appendix still use the localized source/covariance assembly.

### (d) Support, background locality, and inverse decay

- `ZR8Jet`: `QlinStepL`, `D2StepL`, `C2StepL` and their composites have background/input read-ball congruences. `ZR8DataA.C2fullOf_congr_in` and `DY2.C2row_congr` transfer this to raw rows. `DY3.C2row_level0` says the level-zero raw second jet is zero. These facts are selector-independent common-ingredient facts, **not** inverse-propagation claims.
- `ZR8Site.Gp_congr`, `Rproj_congr`, `Wop_congr_both`, `DpiFull_congr`; `ZR8DataB.data_congr`, `G1inv_congr`; `ZR8Data.WellDefG_congr`: exact congruence of the frozen localized assembly under the specified inside/both-endpoint agreement. `RImage_support` is an actual support statement for the site projection image; it is not support of `G` or `G1`.
- `RI2.Dvec_supp`, `Tvec_supp`: support of localized right-inverse construction blocks. `RI2.Tlin_rightInv` and `RI5.rightInv_cfg` do not say the inverse of `Ginv` has finite range.
- `DH1.H_col`, `OL6.H_l2_colR`, `OL9.hHL2_cfg`, `OL7.H1_l2_colR`, `AC_OL10.hH1L2_cfgAC` and its Mixed/Family variants: weighted exponential **column estimates** for localized constrained solution maps. These are meaningful decay estimates, not zero-return theorems.
- `TL3c.Desc.inverse`, `TL13b.HDesc.inverse`, `TL15b.BDLink.G/H/G1inv`, `TL15c.BDLink.H1`: inverse identities under the exact covering/intertwining hypotheses; `AC_SV1.wellDefG_of_coverHyp` descends units. They do not authorize swapping a boundary compression with inversion.
- `GdGen3.Ginv_eq_on_V`, `GdStat.TwoData.H_eq/Delta2_eq/G1inv_eq_on/N1inv_H1_eq`, `DrRed1`: genuine cross-selector comparison results, but all their unit and subspace hypotheses must be retained. `V0` is zero on **every level-zero bond**, not merely an exterior shell.

## 5. What this supplies to the boundary-response problem

With \(A=G_{\rm all}^{-1}\), \(B=G_{\rm in}^{-1}\), \(D=\Delta^{(2)}_{\rm in}\), \(C=B-D\), \(\Theta=A-B\), the chain supplies eventual localized units for \(B,C\), a controlled localized correction, and conditional equality of the literal correction with \(D\). It does **not** supply any of:

- a class-uniform positive lower bound for \(A\), \(A-D\), or \(K_B\);
- a class-uniform bound on \(\|K_B^{-1}\|\) under the guard alone;
- \(B^{-1}\operatorname{range}\Theta\subseteq\texttt{jetInputZero}\), or exact vanishing of \(\Theta C^{-1}DB^{-1}\) on that range;
- the inverse-relative bound \(\|K_B^{-1}(K_C-K_B)\|<1\).

The compiled `GapAt` terminology is especially easy to misread: it is a **unit implication**, not a numeric lower spectral bound. The full-guard results assume the needed additional units and cannot resolve the Ginv-only question. The negative assertion here is only a **mining finding about these declarations**, not a new impossibility theorem or a proof that no source-specific argument can exist.

Nothing here decides either pinned positive goal or its negation, improves the cofinal single-defect construction, or certifies spectral separation.
