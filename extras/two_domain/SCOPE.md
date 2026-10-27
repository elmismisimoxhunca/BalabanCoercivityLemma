# SCOPE (lane two_domain_20261019)

## Question and outcome (facts)
Question (owner): the "literal two-domain transfer" left open by lane thin_layer_20261019 (Sol review: "one-domain reading proved, explicitly defined cap variant proved, literal two-domain transfer NOT proved"; Claude prosecution qualification 2):
operators on a thinner level-0 domain `Omega_0^op` (p.394), regularity class (3.35)/(3.36) read from the larger `Omega_0^cl` (the "<= RM" layer, `Omega_0^op ⊆ Omega_0^cl`).  Does the coercivity headline hold in this form?
Outcome: the two-domain form is a Lean theorem for the union, box, cap, mixed, fixed-factor and frozen forms, with the constants of the one-domain statements; threshold `max R_1 4` for the union form, `R_1` for the others.  Nothing below `R_1` (inherited).
The meeting-clause question: boxes never fail it; disconnected unions fail the plain cut (`plain_cut_fails`, Lean example) and are repaired by a glued far block (`cover_cut`); no condition on the family remains.

## Proved (every `#print axioms` is a subset of [propext, Classical.choice, Quot.sound]: 21 of 23 headline-level prints the triple, `descAt0_of_described` and `descAlt_congr` only [propext, Quot.sound]; `gate_record/axioms_headlines.txt`)
| declaration | content | tag |
|---|---|---|
| `TD1.regBody_mono_b` | regularity with factor `b` implies regularity with every `b' >= b` (`alpha_0, eta >= 0`) | PROVED (Lean) |
| `TD1.glue_side`, `TD1.regBody_glue` | two regular sets at periodic `l^1`-distance `>= 4` form a regular set (single gauge, single `A`; bond, second-difference and curl stencils) | PROVED (Lean) |
| `TD1.far_block_exists` | `y0 ∈ Om1`, `w ∉ Om0`, strict level-0 collar, `4 <= R0` give `v ∈ Om0` with `pdist v y >= 3M+1` for all `y ∈ Om1` (discrete IVT along unit steps) | PROVED (Lean) |
| `TD1.pdist_block_le` | sites of one aligned `M`-block have `pdist u v + 3 <= 3M` | PROVED (Lean) |
| `TD2.cover_cut` | a regular `Sc`-class union of level `j` with nonempty cut to `S.Om 0` lies in a regular `S`-class union whose factor occurs in `F` (cut at level 0; glued far block when the cut misses `B^0(S)`) | PROVED (Lean) |
| `TD2.famTwoDom_union` | `TwoDomFamP unionClass` (printed class), threshold `max R_1 4` | PROVED (Lean) |
| `TD3.famTwoDom_cap`, `TD3.famTwoDom_box` | cap class and box class two-domain headlines (cap route: `ClassCoupledCap` is monotone in `Om 0`) | PROVED (Lean) |
| `TD3.oneDom_of_twoDom`, `oneDomCap_of_twoDom`, `TD4.totalLayer_of_twoDom` | `Sc := S` recovers the one-domain headlines | PROVED (Lean) |
| `TD4.mixedTwoDom`, `totalTwoDom`, `target8TwoDom` | mixed per-cube factors; one factor `c >= 10`; frozen `P428Target8` form (`InstIneq`, `AdmNoBase` at one radius, `SidePow6` from `target8Layer`) | PROVED (Lean) |
| `TD5.two_nonvac_core`, `twodom_nonvac_regime`, `twodom_instance_inequality` | non-vacuity: slab `S` (thin, `AdmSplitNB`) and `Sc` (`Admissible` at `Rb > R`), `Om0(S) ⊊ Om0(Sc)`, curved non-pure-gauge `U` in `ClassCoupled .. Sc`, `Lam != empty`, nonzero positive-energy `Bt`, conclusion at `S` | PROVED (Lean) |
| `TD5.twodom_union_instance_inequality` (with `TD6.regBody_of_M1_union`, `classCoupledU_of_M1`, `famF`) | joint instance for the union class: the same slab towers and curved `U`; `ClassCoupledP unionClass (famF c) Sc` holds (every `Sc`-class union of factor `c` is regular: M1 regime); the family contains the cut-missing cube; `famTwoDom_union` gives the conclusion at `S` | PROVED (Lean) |
| `TD6.plain_cut_fails` | explicit `IsClassUnion` of `Sc` whose cut to `S.Om 0` is nonempty, inside `S.Om 1`, and not a `UnionAt` of index 0 for `S` | PROVED (Lean) |

## Sorry-tree diff
Target "literal two-domain transfer": CLOSED (union/box/cap/mixed/total/frozen).  No `sorry` was ever introduced in the final modules (intermediate skeleton compiled with one `sorry`, closed in the same lane).  No new residual was created.

## Not covered (stated, not elected: each was either closed above or is outside the question)
* Level-0 collar below `R_1` (inherited from lane thin_layer; its evidence list is in that lane's READING.md section 4).  Not attempted here: it is the one-domain question.
* `Sc.Om j ≠ S.Om j` for some `j >= 1`; `Sc.Om 0 ⊉ S.Om 0`.  Different questions (different higher-level domains; a class that does not cover the operator domain).
* A union-class "cap" form (level-0 unions allowed to leave `Om0`, p.408 reading) in two-domain form: not stated; the box-cap form is.
* Inherited conventions (3 dimensions; aligned half-open blocks; periodic `l^1` distance; `CubeBond` = both endpoints; unit-spacing fine lattice) are not changed.

## Self-audit (facts; numbers in `gate_record/`)
See LOG.md "GATES".
