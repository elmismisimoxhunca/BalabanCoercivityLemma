/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.Averaging
import AdalyFormal.Balaban.ScaleLadder

/-!
# Iterated averaging — eq. (43)

Phase-0 REFORM_PROGRAM definitions layer, `PHASE0_DEFS_PLAN.md` item **A2**. Stands alone.

## Source pin

`corpus/pages/CMP98_p24.md` (`verification_status: adjudicated`), eq. (43): *"and if `k`-th order
averaging `Ū^k` is defined at bonds of `Ω^(k)`, then `Ū_c^{k+1} = (Ū^k)‾_c = exp[i Σ_{x∈B(c_-)}
L^{-d} (1/i)log Ū^k(Γ_{c,x})(Ū^k(c))^{-1}] Ū^k(c), c ⊂ Ω^{(k+1)}`, where the contours `Γ_{c,x}` are
defined on the lattice `Ω^(k)`."* — this is `averageAt` from `Averaging.lean` applied recursively:
the order-`(k+1)` average at level `k+1` is `averageAt` fed with the order-`k` average as its
input configuration, threaded down `ScaleLadder.lean`'s tower.

## Scope and disclosed simplification

`Ū^k(Γ_{c,x})`, the source's contour-holonomy evaluation of the level-`k` configuration, needs the
fine-lattice PATH machinery (`Γ_{c_-,x} ∪ [x,x(c)] ∪ Γ_{x(c),c_+}`, CMP98 p.19) that this
standalone module does not build — `Averaging.lean`'s `averageAt` already defers this exact piece
via its abstract `Γ : Center → Site → G` argument. `iterateAverage` below resolves that deferral
the ONLY way available without the path machinery: it reads off the level-`k` configuration's value
AT THE SITE `x` DIRECTLY (`Γ_{c,x} := prev x`), i.e. the DEGENERATE (trivial, single-point) contour,
not a genuine multi-bond path holonomy. **This is a disclosed simplification, not a hidden one** —
it is exactly why this module cannot yet claim the eq. (43) recursion is faithful in full generality
(the real contour is a 3-piece concatenated path per CMP98 p.19, not a point evaluation); wiring the
real path holonomy (`periodicPathHolonomy`-shaped, `Target/ClayStatement.lean:1039`, not imported
here per this module's standalone-first staging) is Phase-1 `Spine.lean` work.

The map `cornerOf j : Level (j+1) → Level j` (representing `c` viewed as a site of the finer
lattice, since `Ū^k(c)` needs a level-`k` value at the coarser point `c`) is likewise EXTRA data
supplied to `iterateAverage` rather than derived — `PHASE0_DEFS_PLAN.md`'s **C1** flags the general
corner-embedding combinatorics as still open; the witness below supplies an explicit, concrete
instance (`c`'s corner = its block's `L^{-1}`-th listed element) rather than a general construction.
-/

namespace AdalyFormal.Balaban

variable {G 𝔤 : Type*} [Group G] [AddCommGroup 𝔤] [Module ℚ 𝔤]

/-- **Eq. (43), iterated averaging.** Given a `ScaleLadder`, abstract `log`/`exp` primitives, a
per-level corner embedding `cornerOf j : Level (j+1) → Level j`, and a base (level-`0`) fine
configuration `U0`, recursively builds the order-`j` averaged configuration for every specified
level `j ≤ ladder.K`. `iterateAverage … 0 _ = U0`; `iterateAverage … (j+1) h` is `averageAt` fed
with the just-built order-`j` configuration, exactly eq. (43)'s recursive shape — see the module
docstring for the one disclosed simplification (`Γ_{c,x} := prev x`, a point evaluation standing in
for the genuine 3-piece contour holonomy). -/
noncomputable def iterateAverage (ladder : ScaleLadder) (log : G → 𝔤) (exp : 𝔤 → G)
    (cornerOf : (j : ℕ) → ladder.Level (j + 1) → ladder.Level j)
    (U0 : ladder.Level 0 → G) :
    (j : ℕ) → j ≤ ladder.K → ladder.Level j → G
  | 0, _ => U0
  | (j + 1), h => fun c =>
      let prev := iterateAverage ladder log exp cornerOf U0 j (by omega)
      averageAt log exp (ladder.block j (by omega)) ladder.L ladder.d
        (fun _ x => prev x) (fun c' => prev (cornerOf j c')) c

/-! ## L7 witness: 2-step iteration on `ScaleLadder.witnessScaleLadder`

Reuses `ScaleLadder.lean`'s `L=2, d=1` witness tower (`Ω^(0)=Fin 4, Ω^(1)=Fin 2, Ω^(2)=Fin 1`) and
`Averaging.lean`'s abelian `G = Multiplicative ℚ` instance. `U0 x := ofAdd(x.1 : ℚ)`
(`0,1,2,3 ↦ 0,1,2,3`), `cornerOf 0 : Fin 2 → Fin 4 := (0 ↦ 0, 1 ↦ 2)` (each block's first listed
site), `cornerOf 1 : Fin 1 → Fin 2 := (0 ↦ 0)`. Hand-computed once and checked against the kernel
below: `U¹(0) = 1/2`, `U¹(1) = 5/2`, `U²(0) = 3/2` — a genuine two-level composition, not merely two
independent copies of the one-step computation in `Averaging.lean`. -/

private noncomputable def witnessU0 : witnessLevel 0 → Multiplicative ℚ :=
  fun x => Multiplicative.ofAdd (x.1 : ℚ)

private def witnessCornerOf : (j : ℕ) → witnessLevel (j + 1) → witnessLevel j
  | 0 => fun c => if c.1 = 0 then (⟨0, by decide⟩ : witnessLevel 0) else ⟨2, by decide⟩
  | 1 => fun _ => (⟨0, by decide⟩ : witnessLevel 1)
  | _ + 2 => fun c => c

/-- **Recursion equation** for `iterateAverage` at a successor level, exposed as a named lemma
(the equation compiler's own defining equation, restated with an explicit `h'` for clean `rw`
under nested applications — proof is `rfl` since two proofs of the same `≤`/`<` proposition are
kernel-equal by proof irrelevance). Used to compose the two witness levels below without
re-unfolding the whole `ScaleLadder` record at each step (which drags in `card_block`'s proof term
and produces spurious application-type-mismatch errors under `unfold`). -/
theorem iterateAverage_succ (ladder : ScaleLadder) (log : G → 𝔤) (exp : 𝔤 → G)
    (cornerOf : (j : ℕ) → ladder.Level (j + 1) → ladder.Level j)
    (U0 : ladder.Level 0 → G) (j : ℕ) (h : j + 1 ≤ ladder.K) (h' : j < ladder.K)
    (c : ladder.Level (j + 1)) :
    iterateAverage ladder log exp cornerOf U0 (j + 1) h c =
      averageAt log exp (ladder.block j h') ladder.L ladder.d
        (fun _ x => iterateAverage ladder log exp cornerOf U0 j (by omega) x)
        (fun c' => iterateAverage ladder log exp cornerOf U0 j (by omega) (cornerOf j c')) c := rfl

/-- The order-`1` (one-step) value at coarse point `0` is `1/2`, matching `Averaging.lean`'s
one-step example exactly (same block, contour, and corner data). -/
theorem witnessIterate_one_zero :
    iterateAverage witnessScaleLadder Multiplicative.toAdd Multiplicative.ofAdd
      witnessCornerOf witnessU0 1 (by decide) (0 : Fin 2)
      = Multiplicative.ofAdd (1 / 2 : ℚ) := by
  rw [iterateAverage_succ (h' := by decide)]
  change
    averageAt Multiplicative.toAdd Multiplicative.ofAdd witnessBlock0 2 1
      (fun _ x => witnessU0 x) (fun c' => witnessU0 (witnessCornerOf 0 c')) (0 : Fin 2)
      = _
  unfold averageAt witnessU0 witnessCornerOf witnessBlock0
  dsimp only
  rw [show ({0, 1} : Finset (Fin 4)) = insert 0 {1} from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- The order-`1` value at coarse point `1` is `5/2`, the other half of the two-point level-`1`
configuration the order-`2` witness composes. -/
theorem witnessIterate_one_one :
    iterateAverage witnessScaleLadder Multiplicative.toAdd Multiplicative.ofAdd
      witnessCornerOf witnessU0 1 (by decide) (1 : Fin 2)
      = Multiplicative.ofAdd (5 / 2 : ℚ) := by
  rw [iterateAverage_succ (h' := by decide)]
  change
    averageAt Multiplicative.toAdd Multiplicative.ofAdd witnessBlock0 2 1
      (fun _ x => witnessU0 x) (fun c' => witnessU0 (witnessCornerOf 0 c')) (1 : Fin 2)
      = _
  unfold averageAt witnessU0 witnessCornerOf witnessBlock0
  dsimp only
  rw [show ({2, 3} : Finset (Fin 4)) = insert 2 {3} from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (5 / 2 : ℚ) = 1 / 2 + 2 from by norm_num, ← ofAdd_add]
  norm_num

/-- The order-`2` (two-step) value at the top coarse point `0` is `3/2` — genuinely composes the
order-`1` values `1/2` and `5/2` proved above at the intermediate level, not a shortcut
recomputation from `U0` directly. -/
example :
    iterateAverage witnessScaleLadder Multiplicative.toAdd Multiplicative.ofAdd
      witnessCornerOf witnessU0 2 (by decide) (0 : Fin 1)
      = Multiplicative.ofAdd (3 / 2 : ℚ) := by
  rw [iterateAverage_succ (h' := by decide)]
  change
    averageAt Multiplicative.toAdd Multiplicative.ofAdd witnessBlock1 2 1
      (fun _ x => iterateAverage witnessScaleLadder Multiplicative.toAdd Multiplicative.ofAdd
        witnessCornerOf witnessU0 1 (by decide) x)
      (fun _ => iterateAverage witnessScaleLadder Multiplicative.toAdd Multiplicative.ofAdd
        witnessCornerOf witnessU0 1 (by decide) (0 : Fin 2))
      (0 : Fin 1) = _
  unfold averageAt witnessBlock1
  dsimp only
  rw [show ({0, 1} : Finset (Fin 2)) = insert 0 {1} from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    witnessIterate_one_zero, witnessIterate_one_one]
  rw [show (3 / 2 : ℚ) = 1 + 1 / 2 from by norm_num, ← ofAdd_add]
  norm_num

end AdalyFormal.Balaban
