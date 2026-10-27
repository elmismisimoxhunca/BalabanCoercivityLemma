# YMX scout: do gaps (A) coverage and (B) p.409/Cor 3.6 affect ymx?

Clone: /tmp/claude-1000/-home-sebastian-projects-project-adaly/f745d75b-6aca-470b-acfe-30e775207baf/scratchpad/ymx
Files: I = theorem_0_complete_account_raw_I.tex, II = ..._II.tex, III = ..._III.tex. All line numbers are in those files.
Read-only scouting. Nothing posted or sent. Quotes are verbatim; anything I could not determine is marked CANNOT TELL.

## Verdicts

- (A) COVERAGE: **does not apply** in Part I, where ymx proves its own coercivity (Lemma 4.4:lem-form-coercivity and the positivity lemma of Ch. 4.14). Both define their class so that coverage is built in or provably holds.
  **Cannot tell / inherited** in Part II (Prop. 5.2:prop-form-positivity and Cor. 5.2:cor-true-pair-positivity). There the positivity is taken from Balaban's printed statement under his per-cube class, and ymx does not check coverage.
- (B) p.409 / Cor 3.6: **applies, unverified by ymx.** ymx never proves that its local sequences satisfy the hypotheses of Cor 3.6. It cites it "as printed". It does not depend on the factor 12 or on a specific smallness constant, so our repaired version (12 or 12ℓ per cube, smallness 12ℓ·M·α0) would suffice for the smallness part. The collar (geometry) part is CANNOT TELL: the needed R ≥ 18ℓ−2 is not checked against their R_0.

## Q1. How they define the regularity class

**Three different classes occur in ymx. They are not one object.**

1. Ch. 4.4, real regular backgrounds U_R (I:4608-4625). The class is global on the whole torus T:
   > "The space U_R of real regular backgrounds consists of the G-valued configurations U on T with the following property: every cube of side at most 6M carries a G-valued gauge transformation u such that ... U^u = exp iξA on that cube, with |A|<2a_U, |∇^ξ A|<2a_U."
   Every bond of T lies in some cube of side ≤ 6M. So every bond is in a regular cube. This is stronger than Balaban's (3.35) and implies coverage.
   - It is obtained from the primed class P' (I:4428-4455), where ymx re-reads Balaban's "O(1)LM" cube condition (1.12) of CMP109. Quote: "In [CMP109 (1.12)] the phrase 'for each cube □⊂X of a size O(1)LM' is read as 'for each cube □⊂X of a size at most oLM'." and "The interpretation 'at most' is the one under which the words 'on the domain Z' ... have content." (I:4447-4449, 4601-4606).
   - So ymx replaces "cubes of exactly the prescribed size" by "all cubes up to that size".
   - P3 (I:4707-4725) shows U_R ⊃ the G-valued factor of P', because "each cube of side at most 6M is contained in one of them [the class cubes of side o·L²·M]".
   - The complexified pairs (U, J) are P_σ: points within σ·(α0, α1) of a base (U, 0) with U ∈ U_R (I:4630-4645). No condition on plaquettes ∂U is imposed on P_σ.
2. Ch. 4.14, the class used for the free-current operator theorem (I:45439-45490). The class is U_R on Ω_0 with three clauses.
   - (u1): "(3.35) read at block size M_1 on the class C_1" (a seam-enlarged cube class).
   - (reg): "Let Q⊂Ω_k be a cube of side M that contains a bond of B^+. For every such Q there is a G-valued gauge transformation u on Q ...", where B^+ is the set of free unit bonds.
   - (reg)^♯: for every box □ of the second cover D^♯ (centred at lattice points of the whole shell X_n), a gauge on □^4∩Ω_0.
   - It adds: "The condition [CMP99b (3.36)] is not among the defining conditions of U_R." So there is no second-order condition.
   - The cover D^♯ is by definition a covering family, and (reg) is imposed on a cube Q for every free bond. This is an explicit coverage condition.
3. Ch. 4.5, the admissible pairs 𝔖 (I:12940-12975). (S1) is Balaban's (3.35) "for every j and every cube □ at level j of the class", with the note "By [p.409] the number O(1) may be taken equal to 12, so that the enlarged cube □^5 ... is contained in one of the cubes on which the condition holds."
   - ymx then proves (S1) from CMP109 (1.12) read as "all cubes up to c12·L·M" (I:13052-13075).
   - Under that reading every cube of side ≤ 17M_1 inside X carries a small gauge. Again coverage is automatic, and the containment of □^5 in a class cube is automatic because every sub-cube is a class cube.
   - "No condition corresponding to (3.36) or (3.38) is imposed" (I:12969).

**Lowest levels (Ch. 4.16).** ymx handles Balaban's p.396 class explicitly (I:52245-52620). It carries the class as a sub-class C_j (N blocks a side, 10 ≤ N ≤ N^♯ = 4M_1^♯/M_1) and proves the (3.35) bound from (reg)^♯ at levels j ∈ {0,1}. See Prop. 4.16:prop-lowest-level-regularity (I:52680-52800): "For every E ∈ C_j there is a box □ ∈ D^♯_j with E ⊂ □^4."
Note the quote: "These are all the cubes of that class when the number written O(1) there is fixed equal to 12." And: "Nothing is asserted here for class cubes of more than N^♯ big blocks a side."

**Part II (true pairs).** Cor. 5.2:cor-true-pair-positivity (II:10188). A "true pair" is (U, J(U)) with U a scaffold minimiser. The regularity input is hypothesis (H̃2) (II:9752):
> "U is regular in the sense of [CMP99b (3.35)--(3.36)], with constant α_0, with respect to the cube classes of both {Ω_j} and {Ω̃_j}."
It is checked in the proof (II:10314-10340):
> "[CMP102b Theorem 1] gives the regularity required in (H̃2) on the cubes of index k+1, which lie in Ω_{k+1} ... On the cubes of index j of older levels the regularity follows from the monotonicity of regularity under passage to sub-cubes ... The bookkeeping of the cubes near the boundary of Ω_{k+1} is part of that monotonicity statement."
This is Balaban's per-cube class. No coverage argument is made.

**Is gap (A) possible for them?**
- Ch. 4.4 and 4.14: no. See Q2.
- Part II: not excluded. The class is Balaban's per-cube class, and the coverage of every bond of the domain Λ by regular class cubes is asserted through "monotonicity", not proved.

## Q2. Coercivity lemma (I:5910, "label 4.4:lem-form-coercivity") and what the perturbation needs

Hypotheses of the lemma:
- (a) the walk hypothesis on U(1), with |||A|||_δ ≤ B everywhere on U(1).
- (b) the positivity lemma at real regular backgrounds.
- (c) a ceiling r_reg := a_1/(3a_U) ≥ 12γ_+^Q/γ_⊕.
- (d) a floor R_P ≥ 32B/γ_0^X.

Conclusion: Re⟨v, A v⟩ ≥ γ_* |v|², with γ_* = (3/4)γ_0^X, on P_{2ρ}, with γ_0^X = γ_⊕/2.

**Base bound at U = 1.** I:5995-5999:
> "The lower bound at the pair (1,0) assumed in (b) is, for Balaban's operators, the content of [CMP96 (2.153), (2.157)]. For operators at U=1, [CMP99b] refers for it to [CMP96 Lemma 2.4]. In this book it is supplied by the lower bound at the trivial background."
They do not use p.428 directly.

**From U = 1 to a general real U ∈ U_R.** This is (b), proved in Ch. 4.14 (I:47400-47520 and 47720-47800), "the positivity lemma on real backgrounds proceeds in seven steps". The argument is IMS localisation over a box cover. Each box needs a gauge with U^u small on a concentric larger cube. The box estimates are:
- Schwarz lemma on the polydisc z ↦ T^□(e^{izηφA}1, 0);
- then a sum over boxes using Σ h_b² = 1.

The coverage requirement is explicit. I:47730-47760: "the cubes b ... for which b'', the concentric enlargement ... contains a bond of B^+" and "there is a cube Q ⊃ (b^{+ℓ})^{+ℓ} of side M, contained in Ω_k and holding a bond of B^+. ... Next we use the regularity condition ... on the cube Q." It uses the hypothesis (A2): dist_∞(Ω_t, Ω_k^c) ≥ 6M, taken from CMP122a pp.178-179, which ymx lists as "stated without proof" (III:111060-111085).

**From (U, 0) to the polydisc P_{2ρ}.** Cauchy estimates on the complex line z ↦ (e^{izξA'}U, zJ): ‖A(𝐔,J) − A(U,0)‖_0 ≤ Bt/(1−t) ≤ γ_0^X/7. This needs the walk bound on U(1) (a), not smallness of U.

**Does perturbation need U near 1 on every bond?**
- It needs U ∈ U_R (a small gauge on every cube of side ≤ 6M). That is: every bond is near 1 after a per-cube gauge.
- Gauge clause (I:5918-5930): "on every cube Q of side 6M there is a G-valued u with U^u = e^{iξA} ...".

**Would our counterexample (U wild on a bond of Ω_0 covered by no regular cube) violate their hypotheses?**
- Ch. 4.4: yes, it is excluded. A bond is always in some cube of side ≤ 6M, which carries a small gauge.
- Ch. 4.14: the wild bond is excluded if it is a free bond (in B^+) or in the seam-enlarged cubes (u1). A wild bond outside every Q and every box would be neither in B^+ nor read by the positivity argument, since the form is on ℓ²(B^+) and the walks are read only in the boxes.
- Part II: the counterexample is not excluded by their text (see Q1).

Their statement of the lemma and U_R are stronger than Balaban's per-cube class with the cubes restricted to nest-indexed ones. So Part I does not inherit (A).

## Q3. Uses of CMP99b Cor 3.6, Thm 3.7, 3.9–3.15, and the p.408–409 construction

**Factor 12.** Only one place:
- I:12951-12957 (Def. 4.5:def-admissible-pairs, (S1)): "By [p.409] the number O(1) may be taken equal to 12, so that the enlarged cube □^5 of [p.409], of side 11𝔐 in level-j units, is contained in one of the cubes on which the condition holds."
- Also I:13058-13062: "The random-walk representations there use gauges defined on the enlarged cubes □^5 [p.409] and boundary conditions imposed outside the enlarged cubes □^8 [p.418]. These have sides 11𝔐 and 17𝔐 ... The cubes of the class in (S1) have side 12𝔐 ≤ 17M_1".
- They note the same in Def. 4.16:def-cube-class (I:52458-52462): "the same paper adds that the number O(1) in the condition (3.35) 'can be taken as equal to 12'", and in (d), (e) that read O(1) as 12.

**They do not rely on it.** The inclusion lemma (I:13005-13094) reproves (S1) from the "all cubes ≤ c12·L·M" reading of CMP109 (1.12), with the ceiling "c12·L·M·B109·α0 ≤ a0". The floors are 17M_1 ≤ c12·L·M. So the p.409 containment is replaced by a stronger hypothesis on the data.

**Cor 3.6 and Theorem 3.11 for localised generators.** I:25069-25075 and 25290-25292 (Prop. 4.6:prop-generator-equality (iv)):
> "The existence of the generators on the regularity class of [(3.35)--(3.38)] is given by [Corollary 3.6], together with the part of [Theorem 3.11] that concerns these generators. By (i) and (ii) its hypotheses and conclusion are the same for the two nests, so it is one and the same statement for both."
- The local sequence is Ω_n(Q) with Ω_g(Q) = Q^{(4)}, Ω_0(Q) ⊂ Q^{(5)}, and collars s_n − s_{n+1} = 2R_0M_0λ_n (I:23797-23830).
- ymx **does not verify** that this local sequence satisfies the hypotheses of Cor 3.6, which is exactly the p.408-409 claim of (B).
- I:28650-28656 lists it as unsettled at outer-seam cubes: "Three properties of a single nest at such cubes are not settled in this section: the applicability of [Corollary 3.6]; the level agreement (LA_□); the gluing of [CMP96]."
- I:13961-13964: for complex configurations they say Cor 3.5 "serves the local propagators at complex configurations as [Corollary 3.6] serves them at real U, and the constructions of [Theorems 3.7, 3.9 and 3.10] are built from these local propagators alone."

**Level 0 and the Λ_0 convention.** Both conventions appear, in different chapters.
- I:23764-23770 (Def. 4.6:def-local-sequence) adopts the p.408 convention for the cover:
  > "We read the corresponding passage of [CMP99b] as saying that the cubes of scale j are those with at least one of their blocks contained in B_j(Λ_j), and that the set T_1∖Ω_1 ... is taken there in place of Λ_0 = Ω_0∖Ω_1."
  And: "for a general Ω_0 the family D_0(Ω) defined by the display may differ from that variant, and the difference plays no role in what follows." This is asserted, not proved.
- I:52470-52480 (Def. 4.16:def-cube-class (iv)) uses the p.396 convention: "At the index 0 the region is 'Λ_0 = Ω_0∖Ω_1, where Ω_0 = {a union of big blocks of the lattice T_1 such that their distances to Ω_1 are ≤ RM}'" and defines a class hull Ω_0^cl.
  They prove (4.16 Prop. (c) and (a)) that class cubes at index 0 with ≤ N^♯ blocks a side lie in C_0 and Ω_0^cl.
  They note that at j = 0 the (3.35) bound uses pointwise weight ℓ_0.

**Levels j used.**
- Ch. 4.6 and 4.16 treat j ∈ {0, 1}, k ≥ 0 and all j ≤ k.
- Part II true pairs: Cor. 5.2 is stated for "k ≥ 0" (II:10188), so the sequence (Ω_j)_{j≤k+1} includes the single-level case. For k=0 they say "For k = 0 the identification is read off [CMP102a]" (II:10285).
- Remark: "Levels j ≤ k. ... the cubes of the cover that lie in W are the standard cubes of side 2M_1L^{j-k}, and the local sequences are concentric cubes" (I:5516-5520). The deep-interior work on W ⊂ Ω_{k+1} avoids seams.

**Smallness.** Part II cor. 5.2: the only condition is "M_1 α_0(γ) ≤ a_X(d, L)" (II:10236-10240; checked at II:10340-10440 as "one upper bound on γ"). Here α_0(γ) = O(1)·B_3·L²(1+β_0)·sup ε_i → 0 as the coupling γ → 0, and γ is chosen after M_1 and L. So any fixed finite factor such as 12ℓ is absorbed, and the repaired smallness 12ℓ·M·α0 ≤ a_1 suffices. In Part I the smallness is also an explicit ceiling: "c12·L·M·B109·α0 ≤ a0" (I:13005-13010), with "2oLMB109α0' ≤ a_reg" (I:5897), imposed after M.

**Geometry (collar).** Their collars, in level-k units:
- dist(Ω_{k+1}, (Ω_k^{(k)})^c) ≥ 8LM Ř_{k+1} ≥ 8L⁴M_1 > R^{bg}M_1 with R^{bg} = L³ (II:10300-10308).
- I:12685-12691: Ω_n a union of cubes of side L^nξM_1 with dist(Ω_n, Ω_{n-1}^c) ≥ L^nξM_1, and M_1 = R'_⋆·𝔐, R'_⋆ ≥ max{R_1, 8}.
- The local-sequence collar is 2R_0M_0 per level, with R_0, M_0 "fixed numbers of [CMP99b]" (value not stated by them).
- Whether any of these meets R ≥ 18ℓ−2 in our units is CANNOT TELL from the text. They never state the (B) requirement.

## Q4. Other places that rely on printed Balaban steps we found problematic

- **Positivity of the exponential-gauge form in Part II.** Prop. 5.2:prop-form-positivity (a) (II:9785-9800). It assumes "the exponential-gauge covariance proposition ... existence of the covariance with its kernel bound, its lower bound ..." and the constants B_0, δ_0 of CMP99b (3.187). The positivity "C_{Q1}^* Δ^{(k)}_{exp} C_{Q1} ≥ (B_0^X K_1^X)^{-1} =: γ_0^X(d, L)" and the proof end (II:9876-9880) says "The estimates of the exponential-gauge covariance proposition and of its estimate lemma are therefore taken here by statement". The proposition itself is not in the files I searched (no hit for the label), so I could not read its hypotheses.
  Also II:10597-10598: "This operator is positive under condition [(3.35)] alone, by [Theorem 3.11]." That is Balaban's printed claim, with no coverage statement. It is a use of the thing gap (A) concerns, in the form "(3.35) alone". The statement is marked as not resting on the true-pair positivity.
- **III:111060-111085** (index of statements printed without proof): four Balaban assertions are counted as taken as printed (CMP119 p.276; CMP122b p.375; CMP122a pp.178-179 admissibility; and "that the initial data lie in the regularity classes of (3.35), (3.37) at the two lowest tower levels"). The last is proved in Part II "as an implication from the inputs displayed with it there", under a floor on M_1^♯.
- **Unchecked claims matching our gaps:** I:4601-4606 ("then (1.12) is void on a domain X too thin to contain such a cube ... no theorem of CMP99b concerns it") shows they saw a related thin-domain issue in CMP109 (1.12), and chose "at most".
- I:105707-105712 (Ch. 4.24): "the background U satisfies [(3.95)] on the cubes visited by the walks below." This is regularity phrased on the walks' cubes, which is a coverage-by-walks formulation.
- **Not located:** the text of the "slice positivity corollary" (II:10445) and the "exponential-gauge covariance proposition". Their absence in the three files, by search for "slice" and "exponential-gauge covariance", means I cannot confirm that they do not rely on p.428.
- No hit for "Omega_0(\square)", "O(1)" claims beyond those already cited, or "\tilde\square^5" in II or III. In I the only tilde-square notation is the 4M cube of CMP96 (I:23487-23500, 25595-25686), identified with □^1 or □^2.

## What I could not determine
- Whether Balaban's p.396 class (as ymx reads it in 4.16) covers every bond of Ω_0 in the first place. ymx does not state or test this for Part II.
- The value or lower bound of R_0, M_0 in their local sequence versus our R ≥ 18ℓ−2.
- Whether "exponential-gauge covariance proposition" hypothesis (H̃2) is applied to a domain where all bonds of Λ lie in a regularity cube. They assert it via monotonicity.
- Whether 4.5's reading "all cubes up to c12·L·M" also holds for cubes meeting the boundary of Ω_0 (their proof says the cube "lies in one cube of side c12LM of (1.12)" but does not say that cube is inside X).
