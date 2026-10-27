# Prosecution of s3-eta-tau (eta / tau-star units)

Draft under review: `AHP/attempts/s3-eta-tau/Units.lean` and `AHP/notes/s3-eta-tau.md`
(draft JSON outcome `drafted-uncompiled`, `compiled: false`, `frozenFilesEdited: false`).
Prosecution method: read-only source audit of every file the draft names, plus the frozen
definitions it quotes and the printed pages it cites. No Lean was run (per constraints);
`Units.lean` was checked by eye. `git status --porcelain` shows only `.bb/` and `AHP/`
untracked: the draft edited nothing frozen and touched no expected file. `Units.lean`
contains no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`implemented_by`/`extern`.

## Verdict (summary)

PARTIAL. The draft's three "Confirm" verdicts (`a⟨B,B⟩`, `bondEnergy`, the pairing
coefficient of the displayed `J` term) and its account of `τ*` survive the audit, subject
to the wording fixes F2, F3, F5, F6 below. The draft's one negative headline —

> "Reject homogeneity inside `BaseDataS.K` … the `Δ^{(2)}` correction inside `G₁` is off by
> one power of `L^{-k}`"

— is **not established and is refuted as stated** (F1): the draft's power count ignores the
level weight `(ell^j)⁻¹` that the code itself puts inside the cross term, and a count that
includes it yields a different power — at the top level, exact homogeneity. The correct
residue is an *open convention question*, not a settled deviation.

## 1. Citation audit — what the draft gets right (confirmed against the frozen text)

| Draft claim | Frozen source | Check |
|---|---|---|
| `firstTerm = P.eta * ⟪τ* B, Ring.inverse (Nmat) (τ* B)⟫` | `ZXG3A.lean:50-52` | exact |
| `genForm = firstTerm - a⟪B,B⟫ - 2⟪H1in (D2in B), Jf⟫` | `ZXG3A.lean:54-56` | exact |
| `eta = ((ell:ℝ)^k)⁻¹` | `ZXR2Wire2.lean:37` | exact |
| `genForm_reduction` cancels `η·(a·ℓ^k·‖B‖²)` against `a⟪B,B⟫` via `η·ℓ^k = 1` | `ZGU1E.lean:48-50, 69-71` | exact; the `calc` block is verbatim what the draft paraphrases |
| `mass_inner : ⟪A, Mass A⟫ = a·ℓ^k·‖Q A‖²` at full support | `ZGU1D.lean:85` | exact |
| `τ*` copies values, `‖τ* B‖ = ‖B‖`, at full support | `ZGU1D.lean:55, 67` | exact; the draft's "no scalar" is a theorem, `tau_adj_apply`/`tau_adj_norm`, correctly scoped to `FullSupp` |
| `Jf = -(JSU2Loc 1 …)`; `JSU2 η = (-i) η⁻³ • Jfield`; `η^d` pairing weight not in the carriers | `ZXR2Wire2.lean:51-53`; `ZIngredientJ.lean:109-115` and header | exact |
| printed pairing `⟨A,J⟩ = Σ_b η^d tr A(b)J(b)` | `sources/corpus/pages/CMP99b_p392.md:101-104` (3.11) | exact |
| printed (3.156) has no `η`, no `τ`; pairing is against `J` | `sources/corpus/pages/CMP99b_p428.md:30-32, 70-80` | exact |
| `D2in` carries `(ell)⁻¹ • hLift …`, a one-step `L` power, not `L^{-k}` | `ZXR2Wire2.lean:90-92` | exact |
| `K A = ⟪A,Dpi A⟫ - 2⟪H (C2 A), J⟫ + ‖T A‖² + ⟪A,Mass A⟫`; `H` built from `G` only (no `J`) | `R2Algebra.lean:146-153` | exact; `G = (Dpi + Ts∘T + Mass)⁻¹`, so `H` is the minimiser map of a purely quadratic form |
| `isG1inv_sub : G₁⁻¹ = G⁻¹ − Δ^{(2)}` with `⟪A,Δ^{(2)}A⟫ = 2⟪H C2 A, J⟫` | `R2Algebra.lean:230` | exact |
| `massW = a·ell^j`; the lane's quadratic operators are the η-free bodies of the printed forms | `ZXR2Ops3.lean:98`; `R2Ops1.lean` CONVENTION header | exact |
| `bondEnergy A = ∑_b ‖A b‖²`; `⟪B,B⟫ = ‖B‖²` is that sum | `RegularUPerturbation.lean:355-356`; `ZGU1E.lean` `hBB` | exact |
| `genFormMut_zeroMode`: rescaling one coefficient breaks the zero-mode law | `ZXG3D2.lean:28` | exact |
| `G1in = η⁻¹ • ι • G₁ • pE`; `unit_of_chain` rewrites `Qin G1in Qin*` as `η⁻¹ • τ N τ*` | `ZXR2Wire2.lean:82-84`, `heq` in `unit_of_chain` | exact |
| `Jf = 0` at flat `U` | `ZXR2Close0a.lean:45` (`Jf_flat`; the note cites no file) | exact |
| `constMode_form` (`PGFC1.lean:70`): `⟪A₀,G₁⁻¹A₀⟫ = a·ℓ^k‖B_c‖²` on a constant mode | `PGFC1.lean` | consistent with the "quadratic part = print/η" reading (see §3) |

`Units.lean` itself: all seven lemmas are correct by inspection (`inv_mul_cancel₀`,
`mul_inv_cancel₀`, `pow_add`, `Nat.sub_add_cancel` with `hd : 3 ≤ d`, the `mul_assoc` /
`mul_left_comm` / `mul_sub` rewrite orders all check out). Honestly labelled uncompiled;
this prosecution did not compile it either.

## 2. F1 (fatal to the headline): the cross term's η-power is not what the draft computes

The draft's `k_cross_not_homogeneous` encodes: lane quadratic part = printed/`η`, lane cross
term = printed cross term, hence `K_lean = η⁻¹(Q_print − 2η C_print)`. The premise "the
cross term uses `Jf = JSU2Loc 1`, whose unweighted pairing equals the full printed pairing
in `d=3`" treats the field `H(C2 A)` being paired against `J` as if its lane values were the
printed values. The code contradicts that for `C2`:

* `ZXR2Sector.lean:109-111`: `C2fullOf G U A` at level `j` is `((ell:ℝ)^j)⁻¹ • C2rawB …` —
  an explicit level weight `L^{-j}` the draft never mentions.
* The same module's header (line 8) states the intent: `C2full` is "the η-free body of
  `C^{(2)} = L^jη C_j^{(2)}`" — i.e. the lane's `C2` is *defined* as the printed object with
  η-powers stripped, which is precisely the "divided by the η-power" relationship the draft
  denies.
* The print agrees that the cross term carries level weights: p.421, the sentence before
  (3.128) (`sources/corpus/pages/CMP99b_p421.md:30`), says that with `H` taken as in (3.126)
  one has `C^{(2)}(A) = L^jη C_j^{(2)}(A)` on `Λ_j`, and (3.136)
  (`sources/corpus/pages/CMP99b_p422.md`) gives `Δ^{(2)}` the explicit weight
  `(L^jη)^{d+1}` per level.

A count including the code's actual level weight, at the top level `j = k` (`L^kη = 1`,
`d = 3`): matching `Q_j(U,ηA)/(L^jη) = Q_j(U)A + C_j^{(2)}(A) + …` against the raw jet
`Q_j(U,ηA) = η·Dq(0)A + η²·½D²q(0)(A,A) + …` gives `C_j^{(2)} = ηL^{-j}·(raw)`, hence
printed `C^{(2)}|_{Λ_k} = L^kη·C_k^{(2)} = η²·(raw)`, while the code stores
`L^{-k}·(raw) = η·(raw)`. Then with the draft's own remaining factors (pairing `η^d`,
`J` values `η^{-3}`, `d = 3`), lane cross term = `η⁻¹` × printed cross term — the **same**
`1/η` scaling as the quadratic parts, i.e. `K_lean = K_print/η`, homogeneous, and the
claimed new deviation evaporates. Other placements of the `η`'s in the (3.14) expansion give
ratio `1` (the draft's) or `η`. Three defensible readings, three different powers.

So: the draft's "off by one power of `L^{-k}`" is one of several mutually incompatible
counts, and the two the draft did not perform are the ones grounded in the code's own level
weight `(ell^j)⁻¹` and the print's own `C^{(2)} = L^jη C_j^{(2)}`. The specific power is an
artifact of an incomplete scaling analysis, presented in the note and in
`Units.lean`'s docstring as if read off the code. Additionally, at levels `j < k` the code's
`L^{-j}` and the print's `(L^jη)^{d+1}` are `k`-dependent in different ways, so no single
global power of `η = L^{-k}` describes the cross term at all — the "one power" phrasing
could at best concern the top level.

What survives of F1's topic: whether the lane's `K` is a homogeneous rescaling of the
printed (3.128) is an **open convention question** (of the same unaudited kind the paper
already flags at `paper.tex:592-594`: "the audit records the inner-product weights as
inherited, not re-derived"). It is not a settled "reject". Note the draft's verdict table is
itself hedged ("Yes … for the pairing as written in `genForm`. Not inside `BaseDataS.K`");
the headline JSON summary ("Reject homogeneity … off by one power of `L^{-k}`") is not.

## 3. F2: the `C`-operator sentence is false as a code description

The note's bondEnergy paragraph: "`C = id - h Q` … and uses the same one-step `ell⁻¹`, not
`L^{-k}`." The code: `Cop = id − hLift ∘ Q` (`ZXR2Unit2.lean:104-107`) with
`hLift = iotaD ∘ H0inv ∘ rhoD` (`ZXR2Unit2.lean:98-102`) — there is **no** `ell⁻¹` anywhere
in `C`; the only explicit `(ell)⁻¹` in this area is inside `D2in`. Moreover `C` is invariant
under any rescaling `Q ↦ cQ` (`(ρ(cQ)ι)⁻¹ρ(cQ) = (ρQι)⁻¹ρQ`), so no power counting applies
to it at all. The correct sentence: "`C` carries no `L`- or `η`-factor (it is scale-invariant
in `Q`), hence is a fortiori `k`-independent." The conclusion the sentence supports ("not an
`η` mismatch") survives.

## 4. F3: the `a_j` recursion is silently set to `a`

The note's displayed equation "`a * ell^j` (`massW`) `= a_j (L^j η)^{d-2}/η^{d-2}`" holds
only if `a_j = a`. The print's (3.24) recursion is `a_{j+1} = a a_j/(aL^{-2} + a_j)`,
`a_1 = a_0 = a` (`R2Ops1.lean` header), so `a_j ≠ a` for `j ≥ 2`. The mass cancellation the
draft confirms is *internal to the lane* (the same `a` appears in `firstTerm`'s mass piece
and in `-a⟪B,B⟫`), and the printed (3.128) itself writes a constant `a‖QA‖²`
(`CMP99b_p421.md:38`), so the confirmation stands — but the print-comparison should be
sourced to (3.128)'s constant `a`, not to (3.24)'s sequence. As written the equation
overstates the match.

## 5. F4: the summary's `J`-row is stronger than the note's own analysis

The note's verdict table concedes the displayed `J` term matches "for the pairing as written
in `genForm`. Not inside `BaseDataS.K`", and the K-section says `H1in` "inherits the same
relative error in the correction". Since `H1in` is built from `G1inv` (`ZXR2Wire2.lean:86-88`,
`R2Algebra.lean:308-309`), the operator fidelity of the displayed `J` term for `J ≠ 0` is
exactly the unresolved F1 question — it cannot simultaneously "match in `d=3`" (summary) and
"inherit the error" (body). Under the homogeneous count of F1 there is no error to inherit.
The summary row should read: pairing normalisation matches in `d=3`; operator fidelity of
`H₁` inside it is the open convention question of F1.

## 6. Minor findings

* F5. The K-section of the note writes "`Jf = JSU2Loc 1`" dropping the minus sign;
  `Jf = -(JSU2Loc 1 …)` (`ZXR2Wire2.lean:52`). The note gets it right elsewhere ("`Jf` is
  `-JSU2Loc 1`"). Cosmetic for units, wrong as a citation.
* F6. The note cites "`OPEN_ITEMS` D-12" for the `η = ℓ^{-k}` convention. The convention item
  is **[REV D-12]** (`paper/OPEN_ITEMS.md:149`); the deviation table's **D12** is the
  unrelated `17ℓ ≤ RM` locality row (`paper.tex` deviation table). Rename the citation.
* `Units.lean`'s docstring calls `eta_mul_pow` "the identity named in `genForm_reduction`";
  in `ZGU1E.lean:48` the identity is an anonymous `have hη`, not a named lemma. Cosmetic.

## 7. Disposition

* **Adopt** (after F2, F3, F5, F6 wording fixes): the three confirmations — `a⟨B,B⟩` and
  `bondEnergy` are the same unweighted unit-bond sums the restored first term's mass piece
  cancels against, the cancellation being exact in the lane because `η·ℓ^k = 1`
  (`ZGU1E.lean:48,69-71`); `τ*` copies values with no scalar at full support
  (`ZGU1D.lean:55,67`); the displayed `J` term's pairing coefficient matches the print in
  `d=3` (`η^d·η^{-3} = 1`). This closes the confirmatory half of S-3 at the level S-3 asked
  ("to be confirmed term by term"), as uncompiled prose-plus-arithmetic evidence.
* **Do not adopt**: "Reject homogeneity inside `BaseDataS.K`; the `Δ^{(2)}` correction is
  off by one power of `L^{-k}`." Replace by: *the relative η-weight of the cross term inside
  the lane's `K` is undetermined; the lane's `C2fullOf` carries `L^{-j}` at level `j` and its
  header calls it the η-free body of the print's `L^jη C_j^{(2)}`, under which `K` is
  homogeneous (`print/η`); other readings give other powers. Resolving it requires a
  convention-level audit of `C2fullOf`/`QfullOf` against (3.14), the p.421 representation
  sentence, and (3.136), which neither this draft nor this prosecution performed.*
* Corollary for the paper: the existing sentence (`paper.tex:590-594`) that the prefactor
  `η` "is described as a normalisation compensating … `G₁ = η⁻¹ιG₁ι*`, and the deviation
  table … has no row for it" is **not** refuted by the draft; had F1's claim held, a new
  deviation-table row would have been owed. It does not hold.
* Nothing here changes `compiled: false`; `Units.lean` remains an uncompiled arithmetic
  model and is not a theorem of the project tree.
