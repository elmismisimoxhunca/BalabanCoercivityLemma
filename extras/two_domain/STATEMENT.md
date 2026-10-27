# STATEMENT (lane two_domain_20261019)

Everything under "Verbatim declarations" is extracted from `src/*.lean` by `tools_gen_statement.py`.  Lean modules: `TD1` (regularity gluing, far block, block geometry), `TD2` (the covering lemma `cover_cut` and the union-class headline),
`TD3` (cap, box; consistency with the one-domain headline), `TD4` (mixed, fixed-factor, frozen forms), `TD5` (non-vacuity: `Om0(S) ⊊ Om0(Sc)`, curved `U`, positive-energy competitor), `TD6` (the plain cut can miss `B^0`),
`TD7` (statement closure and axiom census; no new mathematics).  Every proved declaration depends only on axioms among `propext`, `Classical.choice`, `Quot.sound`: 21 of the 23 headline-level prints use the triple, `descAt0_of_described` and `descAlt_congr` use `propext`, `Quot.sound` only (`gate_record/axioms_headlines.txt`; census `gate_record/census_b1.out`: 1029 roots, 0 with another axiom).
No `sorry`, no new `axiom`; nothing in `formal/` or in a frozen module is edited; modules imported: the thin_layer, level0_class, union_cubes, total, mixed lanes (read-only).

## Question

The operators (`Delta`, `Q`, `G`, ...) are built on a level-0 domain `Omega_0^op` (CMP99b p.394 permission: any union of big blocks containing `Omega_1`, e.g. a thinner layer), while the regularity class (3.35)/(3.36) is the p.396 class defined with the
fixed `<= RM` layer `Omega_0^cl ⊇ Omega_0^op` (cubes, coverage and regularity read from `Omega_0^cl`).  Does the coercivity headline hold in this two-domain form?

## Answer in one paragraph (facts proved; the verdict is the gates')

The statements below hold (kernel-checked) for the class forms listed, with the same constants as the corresponding one-domain statements.  Let `S` be the operator tower (`AdmSplitNB`: `Omega_0^op = S.Om 0` any union of `M`-blocks with the strict level-0 collar `R_0 M`, `R_0 >= R_1`) and `Sc` any second tower
with `Sc.Om j = S.Om j` for `j >= 1` and `S.Om 0 ⊆ Sc.Om 0` (`Omega_0^cl = Sc.Om 0`; `Sc` need not be admissible, block-closed or radial; in particular `Admissible ell M Rc k Sc`, the `<= RM` layer).  If the class hypothesis of the respective form holds for `U` with the
class read from `Sc`, then `InstAtWD ... S Lam U` (or `InstIneq` for the frozen form) holds with the SAME `m_1, a_0, gamma_0`.  Forms: printed class "union of several big blocks" (`famTwoDom_union`, threshold `max R_1 4`), grid-aligned boxes (`famTwoDom_box`), p.408 level-0
boxes with regularity on `cube ∩ Om0` (`famTwoDom_cap`), mixed factors (`mixedTwoDom`), one factor `c >= 10` (`totalTwoDom`), the frozen `P428Target8` (`target8TwoDom`).  Taking `Sc := S` recovers the one-domain headline (`oneDom_of_twoDom`, `oneDomCap_of_twoDom`, `totalLayer_of_twoDom`).
The meeting clause: for boxes the cut `C ∩ Om0(S)` of a level-0 cube meets `B^0(S)` whenever nonempty; for disconnected unions of blocks it does not in general (`plain_cut_fails`, explicit slab example), and the union form repairs it by gluing a far regular `M`-block
(`cover_cut`, `far_block_exists`, `regBody_glue`); no extra condition on the family is needed.  Non-vacuity: `twodom_instance_inequality` (`Om0(S)` strictly inside `Om0(Sc)`, `Sc` admissible at `Rb > R`, curved non-pure-gauge `U` in `ClassCoupled .. Sc`, nonzero positive-energy competitor, conclusion at `S`).
Not proved: any level-0 collar below `R_1` (inherited from lane thin_layer); `Sc.Om j ≠ S.Om j` for some `j >= 1`; an explicit value of `R_1`.

## Paper sentence (draft; plain)

"In the coercivity lemma the operators and the regularity class may use different level-zero domains.  Let `Omega_0^op` be the domain of the operators (any union of `M`-blocks containing `Omega_1` at distance more than `R_0 M` from its complement, `R_0 >= R_1(ell, a)`) and let
`Omega_0^cl ⊇ Omega_0^op` be the level-zero domain used in the definition of the class (3.35)-(3.36), for instance the layer of blocks at distance `<= RM` from `Omega_1`; the domains of the levels `j >= 1` are the same.  If `U` satisfies the regularity conditions on cubes that cover
`Omega_0^cl`, the cubes being read from `Omega_0^cl`, then the conclusion holds for the operators of `Omega_0^op` with the same constants `m_1, a_0, gamma_0` (for the class of unions of big blocks the threshold is `max(R_1, 4)`).  For a cube that is a union of several separated blocks
the part of the cube lying in `Omega_0^op` may fall entirely inside `Omega_1`; the proof then adds to it a block of `Omega_0^op \ Omega_1` far from `Omega_1`, on which `U` is regular by the covering of `Omega_0^cl`.  Layers `Omega_0^op` thinner than `R_1` blocks are not covered by this proof; distances are the periodic `l^1` distance of the lattice."
(Lean: `famTwoDom_union`, `famTwoDom_box`, `famTwoDom_cap`, `mixedTwoDom`, `totalTwoDom`, `target8TwoDom`.)

## Plain reading of the new objects

* `TwoDomFamP Cl` : the headline for the class predicate `Cl`; binders as `FamTorusLayerP Cl` plus `Sc : Tower`, `∀ j >= 1, Sc.Om j = S.Om j`, `S.Om 0 ⊆ Sc.Om 0`; the class hypothesis `ClassCoupledP Cl .. F k Sc ..` is read from `Sc`; the conclusion from `S`.  `Sc` is universally quantified after `S`, never existential.
* `TwoDomCapP`, `MixedTwoDom`, `TotalTwoDom`, `Target8TwoDom` : the same for the cap class, the mixed class, one cube factor, the frozen form (`AdmNoBase` at one radius, `InstIneq`).
* `cover_cut` : a regular `Sc`-class union of level `j` with nonempty cut to `S.Om 0` lies in a regular `S`-class union whose factor occurs in `F`; `regBody_glue` : two regular sets at `l^1`-distance `>= 4` form a regular set (single gauge and `A`);
  `far_block_exists` : under the level-0 collar with `R_0 >= 4`, a site of `Om0` at distance `>= 3M+1` from `Om1`.
* `slabT ell M R T` : the slab tower of lane nonvac_c at level-0 radius `R` (explicit; used by TD5 and TD6).

## What is NOT claimed

* Any level-0 collar below `R_1`; any explicit `R_1`; any statement for towers whose higher-level sets differ (`Sc.Om j ≠ S.Om j`, `j >= 1`); the case `Sc.Om 0 ⊉ S.Om 0`.
* That the print's `Omega_0` of P4 is the second tower of this statement rather than the first (READING.md section 1: one letter, two uses); both readings are Lean statements.
* Inherited conventions are unchanged (3 dimensions, aligned half-open blocks, periodic `l^1` distance, `CubeBond` = both endpoints, fine lattice at unit spacing).
* No ledger row is graded; no `formal/` edit; `S91_ROWS_SUGGESTED.tsv` lists the `∃`-concluding declarations (registrar action for the main loop).

## Verbatim declarations

### `TwoDomFamP` (TD2.lean)
```lean
/-- **the two-domain family headline** for the class predicate `Cl`: the operators are those of the tower `S` (`AdmSplitNB`), the class hypothesis is read from `Sc`
(`Sc.Om j = S.Om j` for `j >= 1`, `S.Om 0 ⊆ Sc.Om 0`). -/
def TwoDomFamP (Cl : ClassPred) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledP Cl ell (ell ^ m) F k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U
```

### `famTwoDom_union` (TD2.lean)
```lean
/-- **`famTwoDom_union`**: the union-class family headline with the operators on `S` (`Omega_0^op`) and the class read from `Sc` (`Omega_0^cl ⊇ Omega_0^op`).  The threshold is `max R_1 4`. -/
theorem famTwoDom_union : TwoDomFamP unionClass := by
```

### `cover_cut` (TD2.lean)
```lean
/-- the key covering lemma: a regular `Sc`-class union of level `j` whose cut to `S.Om 0` is nonempty is contained in a regular `S`-class union of the family `F'`. -/
theorem cover_cut {ell M k R0 : ℕ} {Rs : ℕ → ℕ} {S Sc : Tower L} (hM : 0 < M) (hR0 : 4 ≤ R0)
    (hS : AdmSplitNB ell M R0 Rs k S) (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) (hsub : S.Om 0 ⊆ Sc.Om 0)
    {α₀ η : ℝ} (hα : 0 ≤ α₀) (hη : 0 ≤ η) {U : LinkCfg L} {F : CubeFam L}
    (hc1 : ∀ x ∈ Sc.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeP unionClass ell M F k Sc sites j ∧ x ∈ sites)
    (hc3 : ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ F →
      unionClass L ell M k Sc f sites j → RegBodyH ell M f sites j α₀ η U)
    {C : Set (PeriodicLatticeSite L)} {j f : ℕ} (hCF : (C, j, f) ∈ F) (hCl : IsClassUnion ell M k Sc C j)
    (hne : (C ∩ S.Om 0).Nonempty) :
    ∃ (Q : Set (PeriodicLatticeSite L)) (j' f' : ℕ), IsClassUnion ell M k S Q j' ∧ RegBodyH ell M f' Q j' α₀ η U ∧
      (∃ C' j0, (C', j0, f') ∈ F) ∧ C ∩ S.Om 0 ⊆ Q := by
```

### `regBody_mono_b` (TD1.lean)
```lean
theorem regBody_mono_b {ell M b b' : ℕ} {sites : Set (PeriodicLatticeSite L)} {j : ℕ} {α₀ η : ℝ} {U : LinkCfg L}
    (hb : b ≤ b') (hα : 0 ≤ α₀) (hη : 0 ≤ η) (h : RegBodyH ell M b sites j α₀ η U) : RegBodyH ell M b' sites j α₀ η U := by
```

### `glue_side` (TD1.lean)
```lean
/-- the agreement lemma for one side of the glued pair. `hP`: sites of `W` within `l^1`-distance `3` of a site of `P` are in `P`.
`A` agrees with `A'` on bonds starting in `P`. -/
theorem glue_side {P W : Set (PeriodicLatticeSite L)}
    (hP : ∀ s ∈ P, ∀ t ∈ W, pdist s t ≤ 3 → t ∈ P)
    {A A' : Bond L → Matrix (Fin 2) (Fin 2) ℂ} (hA : ∀ e : Bond L, e.1 ∈ P → A e = A' e) (η : ℝ) :
    (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), x ∈ P → CubeBond W ((x, ν) : Bond L) →
        CubeBond W ((periodicLatticeShift x μ, ν) : Bond L) →
        CubeBond P ((x, ν) : Bond L) ∧ CubeBond P ((periodicLatticeShift x μ, ν) : Bond L) ∧
        A (periodicLatticeShift x μ, ν) = A' (periodicLatticeShift x μ, ν) ∧ A (x, ν) = A' (x, ν)) ∧
    (∀ (μ : Fin 3) (x : PeriodicLatticeSite L), x ∈ P →
        (∀ ν : Fin 3, ν ≠ μ → CurlReads W (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads W x ν μ) →
        (∀ ν : Fin 3, ν ≠ μ → CurlReads P (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads P x ν μ) ∧
        ddA η A x μ = ddA η A' x μ) := by
```

### `regBody_glue` (TD1.lean)
```lean
theorem regBody_glue {ell M b : ℕ} {D E : Set (PeriodicLatticeSite L)} {j : ℕ} {α₀ η : ℝ} {U : LinkCfg L}
    (hsep : ∀ s ∈ D, ∀ t ∈ E, 4 ≤ pdist s t)
    (hD : RegBodyH ell M b D j α₀ η U) (hE : RegBodyH ell M b E j α₀ η U) :
    RegBodyH ell M b (D ∪ E) j α₀ η U := by
```

### `far_block_exists` (TD1.lean)
```lean
/-- **a far block**: if `Om1` contains `y0`, a site `w` lies outside `Om0`, and the strict level-0 collar `R0 * M < pdist x y` holds
(`x ∉ Om0`, `y ∈ Om1`) with `4 <= R0`, then some `v ∈ Om0` has `pdist v y >= 3 M + 1` for every `y ∈ Om1`.  (Discrete intermediate-value argument along unit steps.) -/
theorem far_block_exists {Om0 Om1 : Set (PeriodicLatticeSite L)} {M R0 : ℕ} (hM : 0 < M) (hR : 4 ≤ R0)
    (hcol : ∀ x : PeriodicLatticeSite L, x ∉ Om0 → ∀ y ∈ Om1, R0 * M < pdist x y)
    {y0 : PeriodicLatticeSite L} (hy0 : y0 ∈ Om1) {w : PeriodicLatticeSite L} (hw : w ∉ Om0) :
    ∃ v ∈ Om0, ∀ y ∈ Om1, 3 * M + 1 ≤ pdist v y := by
```

### `pdist_block_le` (TD1.lean)
```lean
/-- sites of one aligned `M`-block are within `l^1`-distance `3 (M-1)` -/
theorem pdist_block_le {M : ℕ} (hM : 0 < M) {u v : PeriodicLatticeSite L} (h : u ∈ blockOf M v) : pdist u v + 3 ≤ 3 * M := by
```

### `descAt0_of_described` (TD3.lean)
```lean
/-- a level-`0` described cube of `Sc` is a `DescribedAt0` box of `S` -/
theorem descAt0_of_described {ell M f k : ℕ} {S Sc : Tower L} (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j)
    {C : Set (PeriodicLatticeSite L)} (hd : DescribedAt ell M f k Sc C 0) : DescribedAt0 ell M f S C := by
```

### `descAlt_congr` (TD3.lean)
```lean
/-- the descriptor of the altered class does not distinguish `S` from `Sc` -/
theorem descAlt_congr {ell M f k : ℕ} {S Sc : Tower L} (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j)
    {C : Set (PeriodicLatticeSite L)} {j : ℕ} :
    DescribedAtAlt ell M f k Sc C j ↔ DescribedAtAlt ell M f k S C j := by
```

### `TwoDomCapP` (TD3.lean)
```lean
/-- the cap headline, two-domain form -/
def TwoDomCapP : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledCap ell (ell ^ m) F k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U
```

### `classCoupledCap_of_two` (TD3.lean)
```lean
theorem classCoupledCap_of_two {ell M k : ℕ} {F : CubeFam L} {S Sc : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hag : ∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) (hsub : S.Om 0 ⊆ Sc.Om 0)
    (h : ClassCoupledCap ell M F k Sc α₀ η U) : ClassCoupledCap ell M F k S α₀ η U := by
```

### `famTwoDom_cap` (TD3.lean)
```lean
theorem famTwoDom_cap : TwoDomCapP := by
```

### `famTwoDom_box` (TD3.lean)
```lean
/-- the box headline, two-domain form (the class of cubes `z + f M ell^j` read from `Sc`) -/
theorem famTwoDom_box : TwoDomFamP boxClass := by
```

### `MixedTwoDom` (TD4.lean)
```lean
/-- the mixed per-cube-factor headline, two-domain form -/
def MixedTwoDom : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Φ : Set ℕ, (∀ f ∈ Φ, 10 ≤ f) → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 →
        ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            MXP.AllC.ClassCoupledΦ ell (ell ^ m) Φ k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U
```

### `mixedTwoDom` (TD4.lean)
```lean
theorem mixedTwoDom : MixedTwoDom := by
```

### `TotalTwoDom` (TD4.lean)
```lean
/-- the fixed-factor headline, two-domain form -/
def TotalTwoDom : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m → ∀ R0 : ℕ, R₁ ≤ R0 → ∀ Rs : ℕ → ℕ, (∀ j, 1 ≤ j → R0 ≤ Rs j) → ∀ RL : ℕ, R0 ≤ RL →
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), AdmSplitNB ell (ell ^ m) R0 Rs k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) RL k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupled ell (ell ^ m) c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstAtWD ell k (by omega) a Lu γ₀ S Lam U
```

### `totalTwoDom` (TD4.lean)
```lean
theorem totalTwoDom : TotalTwoDom := by
```

### `Target8TwoDom` (TD4.lean)
```lean
/-- the frozen `P428Target8` (cube factor `12`, `InstIneq` conclusion), two-domain form: operators on `S` (`AdmNoBase`, one radius), class read from `Sc`. -/
def Target8TwoDom : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), AdalyFormal.ThinLayer.AdmNoBase ell (ell ^ m) R k S →
          ∀ (Sc : Tower (scaleUp ell k Lu)), (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneq ell k (by omega) a Lu γ₀ S Lam U
```

### `target8TwoDom` (TD4.lean)
```lean
theorem target8TwoDom : Target8TwoDom := by
```

### `two_nonvac_core` (TD5.lean)
```lean
theorem two_nonvac_core {ell M R Rb T c : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T)
    (hT : 1 ≤ T) (hcT : c ≤ 2 * T + 1) (hcT' : c ≤ T) (hc10 : 10 ≤ c)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S Sc : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell M Lu ∧ AdmSplitNB ell M R (fun _ => Rb) k S ∧ Admissible ell M Rb k Sc ∧
      (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) ∧ (∀ x, x ∈ S.Om 0 → x ∈ Sc.Om 0) ∧ (∃ p, p ∈ Sc.Om 0 ∧ p ∉ S.Om 0) ∧
      LambdaOK2 ell M Rb k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * (M : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell M c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 := by
```

### `twodom_nonvac_regime` (TD5.lean)
```lean
/-- the two-domain witness at `M = ell^m`: layout scale `T = max Rb c` -/
theorem twodom_nonvac_regime {ell m R Rb c : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hc : 10 ≤ c) (hR : 1 ≤ R) (hRb : R < Rb)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S Sc : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
      2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ AdmSplitNB ell (ell ^ m) R (fun _ => Rb) k S ∧ Admissible ell (ell ^ m) Rb k Sc ∧
      (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) ∧ (∀ x, x ∈ S.Om 0 → x ∈ Sc.Om 0) ∧ (∃ p, p ∈ Sc.Om 0 ∧ p ∉ S.Om 0) ∧
      LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
      0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
      ClassCoupled ell (ell ^ m) c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
      (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
      (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
      Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 :=
```

### `twodom_instance_inequality` (TD5.lean)
```lean
/-- **the two-domain headline applied at the witness**: for every `c >= 10`, `m >= m₁`, level-0 radius `R >= max R₁ 1`, `Rb > R`: the operator tower `S` (thin level-0 domain) and the
class tower `Sc` (the `<= Rb M` layer, `Admissible`) exist, `Om0(S) ⊊ Om0(Sc)`, the curved `U` is in `ClassCoupled .. Sc`, and the conclusion holds for `S` with a nonzero `B~` of positive energy. -/
theorem twodom_instance_inequality (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ (a₀ γ₀ : ℝ), 0 < a₀ ∧ 0 < γ₀ ∧ ∀ c : ℕ, 10 ≤ c → ∀ m : ℕ, m₁ ≤ m →
      ∀ R : ℕ, max R₁ 1 ≤ R → ∀ Rb : ℕ, R < Rb →
      ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S Sc : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
        (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (Bt : Bond Lu → SuTwo),
        2 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ AdmSplitNB ell (ell ^ m) R (fun _ => Rb) k S ∧ Admissible ell (ell ^ m) Rb k Sc ∧
        (∀ j : ℕ, 1 ≤ j → Sc.Om j = S.Om j) ∧ (∀ x, x ∈ S.Om 0 → x ∈ Sc.Om 0) ∧ (∃ p, p ∈ Sc.Om 0 ∧ p ∉ S.Om 0) ∧
        LambdaOK2 ell (ell ^ m) Rb k S Lam ∧
        0 < α₀ ∧ ((c : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
        ClassCoupled ell (ell ^ m) c k Sc α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        (∃ p, p ∈ towerBj S 0) ∧ (∃ p, p ∈ towerBj S 1) ∧ (∃ p, p ∈ towerBj S 2) ∧
        (∃ z, z ∈ S.Om 2 ∧ periodicLatticeShift z 0 ∈ S.Om 2 ∧ plaq U z ≠ 1) ∧
        (¬ ∃ g : PeriodicLatticeSite (scaleUp ell k Lu) → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
        Lam.Nonempty ∧ (LamPrime ell Lam).Nonempty ∧
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧ Bt ≠ 0 ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        γ₀ * bondEnergy Bt ≤
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) := by
```

### `slabT` (TD6.lean)
```lean
/-- the slab tower of lane nonvac_c at level-0 radius `R`, layout scale `T` -/
def slabT (ell M R T : ℕ) : Tower (scaleUp ell 2 (nvcLu M T)) :=
  slab3 (scaleUp ell 2 (nvcLu M T)) (nvcP0 ell M R T) (nvcQ0 ell M R T) (nvcP1 ell M T) (nvcQ1 ell M T) (nvcP2 ell M T) (nvcQ2 ell M T)
```

### `slabT_two` (TD6.lean)
```lean
theorem slabT_two {ell M R Rb T : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T) (hT : 1 ≤ T) :
    AdmSplitNB ell M R (fun _ => Rb) 2 (slabT ell M R T) ∧ Admissible ell M Rb 2 (slabT ell M Rb T) ∧
    (∀ j : ℕ, 1 ≤ j → (slabT ell M Rb T).Om j = (slabT ell M R T).Om j) ∧
    (∀ x, x ∈ (slabT ell M R T).Om 0 → x ∈ (slabT ell M Rb T).Om 0) := by
```

### `plain_cut_fails` (TD6.lean)
```lean
theorem plain_cut_fails {ell M R Rb T : ℕ} (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hRb : R < Rb) (hRbT : Rb ≤ T) (hRT : R ≤ T) (hT : 1 ≤ T) :
    ∃ C : Set (PeriodicLatticeSite (scaleUp ell 2 (nvcLu M T))),
      IsClassUnion ell M 2 (slabT ell M Rb T) C 0 ∧ (C ∩ (slabT ell M R T).Om 0).Nonempty ∧
      C ∩ (slabT ell M R T).Om 0 ⊆ (slabT ell M R T).Om 1 ∧
      ¬ UnionAt ell M 2 (slabT ell M R T) (C ∩ (slabT ell M R T).Om 0) 0 := by
```

