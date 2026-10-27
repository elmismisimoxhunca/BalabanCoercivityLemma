/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import DeltaKWiring

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `J(U)` ON THE TRUE BOND CARRIER, AND THE TWO BOUNDS THAT DECIDE THE SOURCE TERM

`SourceJ.Jsource U : Bond L → Matrix (Fin 2) (Fin 2) ℂ` is the tree's only construction of
CMP99b (3.11)'s `J = D*η⁻²Im∂U` as a FUNCTION OF `U`.  `deltak_wiring`'s `sourceTerm` needs a `J`
in a real inner-product space; `SourceJFaithful.JsourceReal` supplies one by applying a single
REAL COORDINATE functional (`imEntry01`) to the matrix fibre, which its own docstring records as
lossy by dimension count (`8·|Bond L|` down to `|Bond L|`).

**This file supplies the LOSSLESS lift instead.**  `Jsource U b` is Hermitian and traceless
(proved below, §3), so `i·Jsource U b` is skew-Hermitian and traceless, i.e. an element of the
tree's own `SuTwo`, and `J(U)` lands in `BondFnL2 L = PiLp 2 (fun _ : Bond L => SuTwo)` — the TRUE
bond carrier `deltak_wiring` works on.  Multiplication by `i` is the canonical isomorphism between
the Hermitian `𝔤ᶜ` presentation CMP99b/CMP109 use for `Im ∂U` and the skew-Hermitian `𝔰𝔲(2)`
presentation this tree uses; it is a bijection, not a projection.  This closes, at the level of the
CARRIER, the gap `compute/deltak_wiring/SCOPE.md` §4 names as
*"`SourceJ.Jsource`'s carrier is the Hermitian `𝔤ᶜ` convention, not this tree's anti-Hermitian
`SuTwo`."*

## What is then proved, and why it settles the question `deltak_wiring` left open

`deltak_wiring`'s `cdcFormTrue_unbounded_below_in_J` drives the printed form below any prescribed
real number by SCALING a free `J`.  §5 proves that scaling is unreachable for the printed `J`:

* **`EB_Jsource`** — every entry of `Jsource U b` is bounded by `495·δ`, where `δ` bounds the
  entries of `U(b) − 1` over all bonds.  The constant is composed, factor by factor, from the
  telescoping of the four-link plaquette holonomy (`11`), the inverse (`×2`), `Im`'s `1/(2i)`
  (`×1/2`), `π`'s trace subtraction (`×2`), the two-sided conjugation in `D*` (`×4`, plus the
  outflow term `+1`), and the three-term `ν`-sum (`×3`).  No number is chosen.
* **`norm_JsuTwo_le`** — hence `‖J(U)‖ ≤ √(2·|Bond L|)·495·δ` on the true carrier.
* **`norm_JsuTwo_le_uniform`** — and since `δ ≤ 2` for EVERY `SU(2)` configuration whatsoever
  (unitary entries have modulus `≤ 1`), the image of `J(·)` is contained in a ball of a fixed
  radius depending only on the lattice.  **The image of the printed `J` is BOUNDED.**
* **`not_mem_range_JsuTwo_of_norm_gt`** — therefore no gauge configuration produces a `J` of large
  norm: the `J`s `cdcFormTrue_unbounded_below_in_J` exhibits are, past a computable size, outside
  the range of `J(·)` entirely.

The `δ`-linear form of the SAME bound is CMP99b p.419's own sentence
(*"the error terms are small because the function `J = D*η⁻²Im∂U` is small, if `U` satisfies the
condition (3.36)"*) made quantitative: `‖J(U)‖ = O(δ)`, so `J(U) → 0` as the configuration
approaches the flat background.  Combined with `SourceWiredThreshold.lean` this gives the
threshold in `SourceWiredComposed.lean`.

## SOURCE AUDIT of `Jsource` against CMP99b p.392 (done before building; see `SCOPE.md` §2)

`corpus/pages/CMP99b_p392.md`, `verification_status: adjudicated`, render
`corpus/renders/CMP99b_p392-04.png` sha `667c0360…02e5e`:

> `(D^*A)(x) = \sum_{\mu=1}^{d} \eta^{-1}(R(U(x,x-\eta e_\mu))A(x-\eta e_\mu,x) - A(x,x+\eta e_\mu))`
> `= \sum_{\mu=1}^{d} (D_\mu^* A_\mu)(x)`   (3.8)
>
> `(D^*F)(x,x+\eta e_\mu) = (D^*F)_\mu(x) = \sum_{\nu<\mu}(D_\nu^*F_{\nu\mu})(x)`
> `- \sum_{\nu>\mu}(D_\nu^*F_{\mu\nu})(x) = \sum_{\nu=1}^{d}(D_\nu^*F_{\nu\mu})(x)`   (3.9)
>
> where `F_{\mu\nu}(x) = F(p_{\mu\nu}(x))`, and in the last equality above we have assumed that
> `F_{\mu\nu}(x) = -F_{\nu\mu}(x)`.
>
> `\langle A,J\rangle = \sum_{b\subset T_\eta}\eta^d\,\mathrm{tr}\,A(b)J(b)`   (3.11)
>
> where `J = D^*\eta^{-2}\,\mathrm{Im}\,\partial U`, `(\partial U)(p) = U(\partial p)`.

Term-by-term against `SourceJ.lean`: `FnuMu` is (3.9)'s `F_{νμ}` under the assumed antisymmetry;
`DstarDir U ν G x = conjByAmbient (U(x−e_ν,ν))⁻¹ (G(x−e_ν)) − G(x)` is (3.8)'s `(D*_ν G)(x)` with
`η = 1`, and the transport is `R(U(x,x−ηe_ν))` on the nose because the tree's link variable
`U(y,ν)` is the link `y → y+e_ν`, so `U(x,x−ηe_ν) = U(x−ηe_ν,x)⁻¹ = (U(x−e_ν,ν))⁻¹`; `Jfield` is
(3.9)'s final `Σ_ν`; `Jsource U b = Jfield U b.1 b.2` is (3.11)'s bond-indexed `J(b)`.  Two
disclosed conventions: `η = 1` (the whole `Balaban/` chain's unit-lattice convention), and the
projection `π` onto the traceless algebra, which CMP99b (3.11) does not display but CMP109 (1.8)
does (`J_j = D*_{Ũ_j}^{ξ*}ξ⁻²π Im ∂U_j`, "where `π` denotes the projection ... onto the algebra
`𝔤ᶜ`") — `π` is load-bearing HERE, since without it `Im ∂U` is Hermitian but not traceless and the
`𝔰𝔲(2)` lift of §4 would not exist.

**NOT claimed:** that (3.11)'s PAIRING `Σ_b η^d tr A(b)J(b)` (normalized trace, Hermitian `A`)
equals this tree's `inner ℝ` on `BondFnL2` (`hsInner X Y = −½ Re Tr(XY)`, skew-Hermitian carrier).
Those differ by the same factor `i` and by trace normalization.  Every conclusion below is
invariant under a positive real rescaling of `J`, and any such constant is absorbed in the
`c₂`/`γ₁` accounting of `SourceWiredThreshold.lean`; it is NOT silently assumed to be `1`.
-/

namespace AdalyFormal.Balaban.SourceWiredJ

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwo conjByAmbient conjByAmbient_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield Jsource)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `EB`: an entrywise bound, and its algebra

One predicate, eight closure lemmas.  Every constant downstream is produced by composing these,
so no number in this file is written by hand at the place it is used. -/

/-- **`EB C X`**: every entry of the `2×2` complex matrix `X` has norm at most `C`. -/
def EB (C : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop := ∀ i j, ‖X i j‖ ≤ C

theorem EB.mono {C D : ℝ} {X : Matrix (Fin 2) (Fin 2) ℂ} (h : EB C X) (hCD : C ≤ D) : EB D X :=
  fun i j => (h i j).trans hCD

theorem EB.nonneg {C : ℝ} {X : Matrix (Fin 2) (Fin 2) ℂ} (h : EB C X) : 0 ≤ C :=
  le_trans (norm_nonneg _) (h 0 0)

theorem EB_zero {C : ℝ} (hC : 0 ≤ C) : EB C (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro i j; simpa using hC

theorem EB.add {a b : ℝ} {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) (hY : EB b Y) :
    EB (a + b) (X + Y) := by
  intro i j
  rw [Matrix.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (hX i j) (hY i j))

theorem EB.sub {a b : ℝ} {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) (hY : EB b Y) :
    EB (a + b) (X - Y) := by
  intro i j
  rw [Matrix.sub_apply]
  exact (norm_sub_le _ _).trans (add_le_add (hX i j) (hY i j))

theorem EB.neg {a : ℝ} {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) : EB a (-X) := by
  intro i j; rw [Matrix.neg_apply, norm_neg]; exact hX i j

theorem EB.smul (c : ℂ) {a : ℝ} {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) :
    EB (‖c‖ * a) (c • X) := by
  intro i j
  rw [Matrix.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hX i j) (norm_nonneg c)

/-- The FACTOR 2 in the product rule is the matrix dimension: a `2×2` entry of `XY` is a sum of
`2` products.  Derived, not chosen. -/
theorem EB.mul {a b : ℝ} {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) (hY : EB b Y) :
    EB (2 * (a * b)) (X * Y) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  have h0 : ‖X i 0 * Y 0 j‖ ≤ a * b := by
    rw [norm_mul]; exact mul_le_mul (hX i 0) (hY 0 j) (norm_nonneg _) hX.nonneg
  have h1 : ‖X i 1 * Y 1 j‖ ≤ a * b := by
    rw [norm_mul]; exact mul_le_mul (hX i 1) (hY 1 j) (norm_nonneg _) hX.nonneg
  have := norm_add_le (X i 0 * Y 0 j) (X i 1 * Y 1 j)
  linarith

theorem EB.conjTranspose {a : ℝ} {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) : EB a Xᴴ := by
  intro i j
  rw [Matrix.conjTranspose_apply, norm_star]
  exact hX j i

theorem EB_one : EB 1 (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- `‖tr X‖ ≤ 2·C`: the `2` is again the dimension (`tr` of a `2×2` is a sum of two entries). -/
theorem EB.trace_le {a : ℝ} {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) :
    ‖Matrix.trace X‖ ≤ 2 * a := by
  rw [Matrix.trace_fin_two]
  have := norm_add_le (X 0 0) (X 1 1)
  have h0 := hX 0 0
  have h1 := hX 1 1
  linarith

/-! ## §2 — the two facts about `SU(2)` link variables that start the chain -/

/-- **Every entry of an `SU(2)` matrix has modulus `≤ 1`** — from `UᴴU = 1`, whose `(j,j)` entry
says the `j`-th column is a unit vector. -/
theorem EB_su2 (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    EB 1 (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro i j
  have h : (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp g.2.1
  have hjj := congrFun (congrFun h j) j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at hjj
  simp only [Matrix.conjTranspose_apply] at hjj
  have e0 : star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 j) * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 j
      = ((‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 j‖ : ℝ) : ℂ) ^ 2 :=
    Complex.conj_mul' _
  have e1 : star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 j) * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 j
      = ((‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 j‖ : ℝ) : ℂ) ^ 2 :=
    Complex.conj_mul' _
  rw [e0, e1] at hjj
  have hr : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 j‖ ^ 2
      + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 j‖ ^ 2 = 1 := by
    exact_mod_cast hjj
  have n0 := norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 j)
  have n1 := norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 j)
  have hi : i = 0 ∨ i = 1 := by fin_cases i
                                · exact Or.inl rfl
                                · exact Or.inr rfl
  rcases hi with h | h <;> subst h <;> nlinarith [hr, n0, n1]

/-- The crude, ALWAYS-TRUE deviation bound: `δ = 2` works for every configuration. -/
theorem EB_su2_dev_two (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    EB 2 ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) :=
  ((EB_su2 g).sub EB_one).mono (by norm_num)

/-- **Telescoping one factor**: `gh − 1 = g(h − 1) + (g − 1)`. -/
theorem EB_group_dev_mul (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) {dg dh : ℝ}
    (hg : EB dg ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1))
    (hh : EB dh ((h : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :
    EB (2 * (1 * dh) + dg)
      (((g * h : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have hcoe : ((g * h : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) :=
    Submonoid.coe_mul (Matrix.specialUnitaryGroup (Fin 2) ℂ) g h
  have hid : (g : Matrix (Fin 2) (Fin 2) ℂ) * (h : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = (g : Matrix (Fin 2) (Fin 2) ℂ) * ((h : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        + ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
    noncomm_ring
  rw [hcoe, hid]
  exact ((EB_su2 g).mul hh).add hg

/-- **The inverse doubles the deviation**: `g⁻¹ − 1 = −g⁻¹(g − 1)`. -/
theorem EB_group_dev_inv (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) {d : ℝ}
    (hg : EB d ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :
    EB (2 * (1 * d))
      (((g⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have hinvmul : ((g⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel]
    exact Submonoid.coe_one _
  have hid : ((g⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1
      = -(((g⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
          * ((g : Matrix (Fin 2) (Fin 2) ℂ) - 1)) := by
    rw [mul_sub, hinvmul, mul_one, neg_sub]
  rw [hid]
  exact ((EB_su2 g⁻¹).mul hg).neg

/-! ## §3 — the chain, from the link deviation to `J`'s entries

`δ` is carried as a HYPOTHESIS on the configuration, so the same chain serves both the uniform
bound (`δ := 2`, always true) and the smallness statement (`δ` small). -/

/-- **`hol(∂p) − 1` is `11·δ`.**  Four links telescoped: `δ`, then `3δ`, `7δ`, `11δ` — the two
inverses contributing `2δ` each. -/
theorem EB_holonomyElem_dev
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
    (p : PeriodicLatticePlaquette L) :
    EB (11 * δ) ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  have s12 := EB_group_dev_mul (U (p.1, p.2.1.1))
    (U (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) (hdev _) (hdev _)
  have s123 := EB_group_dev_mul _ ((U (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹) s12
    (EB_group_dev_inv _ (hdev _))
  have s1234 := EB_group_dev_mul _ ((U (p.1, p.2.1.2))⁻¹) s123 (EB_group_dev_inv _ (hdev _))
  refine s1234.mono (le_of_eq ?_)
  ring

theorem EB_holonomyElemInv_dev
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
    (p : PeriodicLatticePlaquette L) :
    EB (22 * δ) ((holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
  refine (EB_group_dev_inv _ (EB_holonomyElem_dev U hdev p)).mono (le_of_eq ?_)
  ring

/-- **`Im U(∂p)` is `(33/2)·δ`** — `(1/(2i))` contributes exactly `1/2`, and
`hol − hol⁻¹ = (hol − 1) − (hol⁻¹ − 1)`. -/
theorem EB_imHolonomy
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
    (p : PeriodicLatticePlaquette L) :
    EB ((33 / 2) * δ) (imHolonomy U p) := by
  have hsplit : (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ)
      - (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ)
      = ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        - ((holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by abel
  have hd := (EB_holonomyElem_dev U hdev p).sub (EB_holonomyElemInv_dev U hdev p)
  rw [← hsplit] at hd
  have hI : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_mul, Complex.norm_I]
    norm_num
  have := hd.smul (1 / (2 * Complex.I) : ℂ)
  rw [hI] at this
  refine this.mono (le_of_eq ?_)
  ring

/-- **`π` doubles**: `π(X) = X − (tr X/2)·1`, and `‖tr X/2‖ ≤ C`. -/
theorem EB_piProj {a : ℝ} {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : EB a X) : EB (2 * a) (piProj X) := by
  have h1 : EB a ((Matrix.trace X / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    refine (EB_one.smul (Matrix.trace X / 2)).mono ?_
    have ht := hX.trace_le
    have : ‖Matrix.trace X / 2‖ = ‖Matrix.trace X‖ / 2 := by
      rw [norm_div]; norm_num
    rw [this]
    linarith
  have h2 : EB (a + a) (X - (Matrix.trace X / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := hX.sub h1
  refine h2.mono (le_of_eq ?_)
  ring

theorem EB_FnuMu
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    EB (33 * δ) (FnuMu U ν μ y) := by
  have hδ0 : 0 ≤ δ := (hdev (y, ν)).nonneg
  unfold FnuMu
  split_ifs with h1 h2
  · refine (EB_piProj (EB_imHolonomy U hdev _)).mono (le_of_eq ?_); ring
  · refine ((EB_piProj (EB_imHolonomy U hdev _)).neg).mono (le_of_eq ?_); ring
  · exact EB_zero (by linarith)

/-- **`D*_ν` costs `×4 + 1`**: two-sided conjugation `V·X·Vᴴ` is two matrix products (`2·2 = 4`),
plus the un-transported outflow term. -/
theorem EB_DstarDir
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν : Fin 3) {c : ℝ} {G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ}
    (hG : ∀ y, EB c (G y)) (x : PeriodicLatticeSite L) :
    EB (5 * c) (DstarDir U ν G x) := by
  have hV : EB 1 (((U (periodicLatticeShiftBack x ν, ν))⁻¹ :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    EB_su2 _
  have hconj : EB (2 * (2 * (1 * c) * 1))
      (conjByAmbient (U (periodicLatticeShiftBack x ν, ν))⁻¹ (G (periodicLatticeShiftBack x ν))) := by
    rw [conjByAmbient_apply]
    exact (hV.mul (hG _)).mul hV.conjTranspose
  have hd := hconj.sub (hG x)
  refine hd.mono (le_of_eq ?_)
  ring

/-- **`J`'s entries are `495·δ`** — `3` (the `ν`-sum) `× 5` (`D*_ν`) `× 2` (`π`) `× 33/2`
(`Im` of the telescoped holonomy). -/
theorem EB_Jfield
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1))
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    EB (495 * δ) (Jfield U x μ) := by
  have hδ0 : 0 ≤ δ := (hdev (x, μ)).nonneg
  have hterm : ∀ ν : Fin 3,
      EB (165 * δ) (if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x) := by
    intro ν
    split_ifs with h
    · exact EB_zero (by linarith)
    · refine (EB_DstarDir U ν (fun y => EB_FnuMu U hdev ν μ y) x).mono (le_of_eq ?_); ring
  intro i j
  have hsum : (Jfield U x μ) i j
      = ∑ ν : Fin 3, (if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x) i j := by
    show (∑ ν : Fin 3, (if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x)) i j = _
    simp [Matrix.sum_apply]
  rw [hsum]
  calc ‖∑ ν : Fin 3, (if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x) i j‖
      ≤ ∑ _ν : Fin 3, (165 * δ) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => hterm ν i j)
    _ = 495 * δ := by simp; ring

theorem EB_Jsource
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)) (b : Bond L) :
    EB (495 * δ) (Jsource U b) :=
  EB_Jfield U hdev b.1 b.2

#print axioms EB_Jsource

/-! ## §4 — `Jsource` is Hermitian and traceless, hence `i·Jsource` lies in `𝔰𝔲(2)` -/

/-- **`HT X`**: `X` is Hermitian and traceless — the `𝔤ᶜ` presentation CMP109 (1.8)'s `π` projects
onto. -/
def HT (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop := Xᴴ = X ∧ Matrix.trace X = 0

theorem HT.neg {X : Matrix (Fin 2) (Fin 2) ℂ} (h : HT X) : HT (-X) :=
  ⟨by rw [Matrix.conjTranspose_neg, h.1], by rw [Matrix.trace_neg, h.2, neg_zero]⟩

theorem HT.sub {X Y : Matrix (Fin 2) (Fin 2) ℂ} (hX : HT X) (hY : HT Y) : HT (X - Y) :=
  ⟨by rw [Matrix.conjTranspose_sub, hX.1, hY.1], by rw [Matrix.trace_sub, hX.2, hY.2, sub_zero]⟩

theorem HT_zero : HT (0 : Matrix (Fin 2) (Fin 2) ℂ) := ⟨by simp, by simp⟩

/-- `Im U(∂p)` is Hermitian: `hol⁻¹ = holᴴ` and `conj(1/(2i)) = −1/(2i)`. -/
theorem imHolonomy_isHermitian
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) : (imHolonomy U p)ᴴ = imHolonomy U p := by
  have hinv : ((holonomyElemInv U p : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl
  unfold imHolonomy
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hinv,
    Matrix.conjTranspose_conjTranspose]
  have hc : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I) : ℂ) := by
    simp
  rw [hc]
  module

/-- `π` lands in `HT`, for any Hermitian input — this is the step that makes the `𝔰𝔲(2)` lift
possible, and it is exactly CMP109 (1.8)'s explicit `π`. -/
theorem HT_piProj {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : Xᴴ = X) : HT (piProj X) := by
  have htr : star (Matrix.trace X) = Matrix.trace X := by
    have h := congrArg Matrix.trace hX
    rwa [Matrix.trace_conjTranspose] at h
  have h2 : star (Matrix.trace X / 2 : ℂ) = Matrix.trace X / 2 := by
    rw [star_div₀, htr]
    norm_num
  constructor
  · unfold piProj
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hX, h2]
  · unfold piProj
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp

theorem HT_FnuMu (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) : HT (FnuMu U ν μ y) := by
  unfold FnuMu
  split_ifs
  · exact HT_piProj (imHolonomy_isHermitian U _)
  · exact (HT_piProj (imHolonomy_isHermitian U _)).neg
  · exact HT_zero

theorem HT_conjByAmbient (V : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : HT X) : HT (conjByAmbient V X) := by
  have hVV : (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (V : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.2.1
  constructor
  · rw [conjByAmbient_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hX.1, Matrix.mul_assoc]
  · rw [conjByAmbient_apply, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul, hX.2]

theorem HT_DstarDir (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν : Fin 3) {G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ} (hG : ∀ y, HT (G y))
    (x : PeriodicLatticeSite L) : HT (DstarDir U ν G x) :=
  (HT_conjByAmbient _ (hG _)).sub (hG x)

theorem HT_Jfield (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : HT (Jfield U x μ) := by
  have hterm : ∀ ν : Fin 3,
      HT (if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x) := by
    intro ν
    split_ifs
    · exact HT_zero
    · exact HT_DstarDir U ν (fun y => HT_FnuMu U ν μ y) x
  show HT (∑ ν : Fin 3, _)
  constructor
  · rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun ν _ => (hterm ν).1
  · rw [Matrix.trace_sum]
    exact Finset.sum_eq_zero fun ν _ => (hterm ν).2

theorem HT_Jsource (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b : Bond L) : HT (Jsource U b) := HT_Jfield U b.1 b.2

#print axioms HT_Jsource

/-! ## §5 — the lossless lift `J(U) : BondFnL2 L`, and its two norm bounds -/

/-- **`i·J` is `𝔰𝔲(2)`-valued.**  The canonical Hermitian → skew-Hermitian isomorphism, applied
to the traceless `J` of §4. -/
theorem I_smul_Jsource_mem
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (b : Bond L) :
    (Complex.I • Jsource U b) ∈ suTwo := by
  obtain ⟨h1, h2⟩ := HT_Jsource U b
  constructor
  · rw [Matrix.conjTranspose_smul, h1]
    simp [Complex.conj_I]
  · rw [Matrix.trace_smul, h2]
    simp

/-- **`J(U)` ON THE TRUE BOND CARRIER** — CMP99b (3.11)'s source, as a function of the gauge
configuration, in `BondFnL2 L = PiLp 2 (fun _ : Bond L => SuTwo)`.  Lossless: `Complex.I • ·` is a
bijection between the Hermitian and skew-Hermitian traceless presentations. -/
noncomputable def JsuTwo (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L :=
  WithLp.toLp 2 (fun b : Bond L => (⟨Complex.I • Jsource U b, I_smul_Jsource_mem U b⟩ : SuTwo))

theorem JsuTwo_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b : Bond L) :
    ((WithLp.ofLp (JsuTwo U) b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) = Complex.I • Jsource U b :=
  rfl

/-- **`J(U)` vanishes at the flat background** — inherited from `SourceJ.Jsource_trivialU_eq_zero`,
the non-degeneracy control that makes the `δ`-linear bound below non-vacuous in the right
direction. -/
theorem JsuTwo_trivialU : JsuTwo (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) = 0 := by
  ext b i j
  show (Complex.I • Jsource (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) b) i j = _
  rw [AdalyFormal.Balaban.SourceJ.Jsource_trivialU_eq_zero b]
  simp

/-- Per bond: `‖J(U)(b)‖² ≤ 2·(495δ)²`, from `hsInner X X = ½Σ|Xᵢⱼ|²`. -/
theorem norm_sq_JsuTwo_bond_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)) (b : Bond L) :
    ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2 ≤ 2 * (495 * δ) ^ 2 := by
  have hEB : EB (495 * δ) (Complex.I • Jsource U b) := by
    have hs := (EB_Jsource U hdev b).smul Complex.I
    rw [Complex.norm_I] at hs
    refine hs.mono (le_of_eq ?_)
    ring
  have hnorm : ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2
      = AdalyFormal.Balaban.SuTwoInner.hsInner (WithLp.ofLp (JsuTwo U) b)
          (WithLp.ofLp (JsuTwo U) b) := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [hnorm, AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_sumNormSq]
  have e : ∀ i j, ((WithLp.ofLp (JsuTwo U) b : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) i j
      = (Complex.I • Jsource U b) i j := by
    intro i j; rw [JsuTwo_apply]
  have hb : ∀ i j, Complex.normSq (((WithLp.ofLp (JsuTwo U) b : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ (495 * δ) ^ 2 := by
    intro i j
    rw [e i j, Complex.normSq_eq_norm_sq]
    have := hEB i j
    nlinarith [this, norm_nonneg ((Complex.I • Jsource U b) i j), hEB.nonneg]
  have h00 := hb 0 0
  have h01 := hb 0 1
  have h10 := hb 1 0
  have h11 := hb 1 1
  linarith

/-- **THE NORM BOUND.**  `‖J(U)‖ ≤ √(2·|Bond L|)·495·δ` on the true bond carrier. -/
theorem norm_JsuTwo_le
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hdev : ∀ b : Bond L, EB δ ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := by
  have hδ0 : 0 ≤ δ := by
    classical
    exact (hdev (Classical.arbitrary (Bond L))).nonneg
  have hC : (0 : ℝ) ≤ 495 * δ := by linarith
  rw [PiLp.norm_eq_of_L2]
  have hsum : ∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2
      ≤ (Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2) := by
    calc ∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2
        ≤ ∑ _b : Bond L, (2 * (495 * δ) ^ 2) :=
          Finset.sum_le_sum fun b _ => norm_sq_JsuTwo_bond_le U hdev b
      _ = (Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2) := by
          simp [Finset.sum_const, Finset.card_univ]
  have hfin : Real.sqrt ((Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2))
      = Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := by
    rw [show ((Fintype.card (Bond L) : ℝ)) * (2 * (495 * δ) ^ 2)
        = (2 * (Fintype.card (Bond L) : ℝ)) * (495 * δ) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hC]
  calc Real.sqrt (∑ b : Bond L, ‖(WithLp.ofLp (JsuTwo U) b : SuTwo)‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card (Bond L)) * (2 * (495 * δ) ^ 2)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (2 * (Fintype.card (Bond L))) * (495 * δ) := hfin

/-- **THE IMAGE OF `J(·)` IS BOUNDED — for EVERY `SU(2)` configuration, with no regularity
assumption at all.**  `δ = 2` always works because unitary entries have modulus `≤ 1`. -/
theorem norm_JsuTwo_le_uniform
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ‖JsuTwo U‖ ≤ Real.sqrt (2 * (Fintype.card (Bond L))) * 990 := by
  have h := norm_JsuTwo_le U (δ := 2) (fun b => EB_su2_dev_two (U b))
  have e : (495 : ℝ) * 2 = 990 := by norm_num
  rwa [e] at h

#print axioms norm_JsuTwo_le
#print axioms norm_JsuTwo_le_uniform

/-! ## §6 — the consequence for `deltak_wiring`'s free-`J` counterexample

`cdcFormTrue_unbounded_below_in_J` produces, for each prescribed real `c`, a `J` of the form
`t • J₀` with `t` growing without bound.  §5 says such `J`s leave the range of `J(·)`. -/

/-- **NO GAUGE CONFIGURATION PRODUCES A LARGE SOURCE.**  Past the uniform radius, a vector is not
`J(U)` for ANY `U` — so a counterexample that needs a large `‖J‖` is not a counterexample about the
printed, `U`-determined `J`. -/
theorem not_mem_range_JsuTwo_of_norm_gt (J : BondFnL2 L)
    (hJ : Real.sqrt (2 * (Fintype.card (Bond L))) * 990 < ‖J‖)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    JsuTwo U ≠ J := by
  intro h
  have := norm_JsuTwo_le_uniform U
  rw [h] at this
  linarith

#print axioms not_mem_range_JsuTwo_of_norm_gt

end AdalyFormal.Balaban.SourceWiredJ
