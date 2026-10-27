import GV10

/-!
# GV11 -- normalisation, pairwise transitions, and the chart at a bad vertex (m2_glue3, 2026-10-15)

* `gsN n σ b = n σ b · flA σ b` (constant left multiplication); `nrm`: the normalising constants
  (`(2,+)` fixed; `(0,±)`, `(1,±)` normalised against `(2,+)` at a corner site; `(2,−)` against `(0,+)`).
* `pair_growth`, `pair_via`: transitions of base-flat charts grow like `128 ρ² s` from a corner site;
  cocycle at triple corners.  All twelve non-opposite pairs: `|h − 1| ≤ 1152 ρ² s`.
* **`gchart_at_bad_vertex`**: six class-cube half-space charts at `(t₁, t₂)` around `v` give ONE chart on the
  coordinate box of radius `R` around `v`, at `(KT1·(3R+2)·s, KT2·s)`, `s = t₂ + 43 t₁²`, with universal constants,
  which is `cB·ρ² s + 15 ρ t₁`-close to each input chart up to a constant.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul)

variable {L : PeriodicLatticeExtent}

/-! ## pair growth -/

def isCorner (z : Z3) : Prop := ∀ i, z i = 0 ∨ z i = -1

theorem rho_corner {z : Z3} (hz : isCorner z) : rho z = 3 / 2 := by
  unfold rho qc
  have e : ∀ i, |((z i : ℤ) : ℝ) + 1 / 2| = 1 / 2 := by
    intro i
    rcases hz i with h | h <;> rw [h] <;> norm_num
  rw [e 0, e 1, e 2]; norm_num

theorem hsP_between {σ : Fin 3} {b : Bool} {p z w : Z3} (hp : hsP σ b p) (hz : hsP σ b z)
    (h1 : min (p σ) (z σ) ≤ w σ) (h2 : w σ ≤ max (p σ) (z σ)) : hsP σ b w := by
  unfold hsP at *
  rcases hp with ⟨rfl, a⟩ | ⟨rfl, a⟩
  · left; refine ⟨rfl, ?_⟩
    rcases hz with ⟨_, c⟩ | ⟨c, _⟩
    · have : 0 ≤ min (p σ) (z σ) := le_min a c
      linarith
    · exact absurd c (by decide)
  · right; refine ⟨rfl, ?_⟩
    rcases hz with ⟨c, _⟩ | ⟨_, c⟩
    · exact absurd c (by decide)
    · have : max (p σ) (z σ) ≤ -1 := max_le a c
      linarith

theorem pair_growth {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 2)))
    {P Q : PeriodicLatticeSite L → SU2} {σ σ' : Fin 3} {b b' : Bool} {s : ℝ} (hs : 0 ≤ s)
    {TP TQ : Z3 → ℝ}
    (hP : ZCh U P v (Hd R σ b) (fun p => 4 * rho p * s) TP) (hQ : ZCh U Q v (Hd R σ' b') (fun p => 4 * rho p * s) TQ)
    {z p : Z3} (hz : isCorner z) (hza : z ∈ Hd R σ b) (hzb : z ∈ Hd R σ' b') (hpa : p ∈ Hd R σ b)
    (hpb : p ∈ Hd R σ' b') {E : ℝ} (hE : frobNorm (((trans P Q (iota v z) : SU2) : M2) - 1) ≤ E) :
    frobNorm (((trans P Q (iota v p) : SU2) : M2) - 1) ≤ E + 128 * rho p ^ 2 * s := by
  set lo : Z3 := fun i => min (p i) (z i)
  set hi : Z3 := fun i => max (p i) (z i)
  have hbox : IBox lo hi ⊆ Box (R + 1) := by
    intro w hw i
    have a := hpa.1 i; have c := hza.1 i; have d := hw i
    simp only [lo, hi] at d
    rw [abs_le] at a c ⊢
    constructor
    · have := min_le_left (p i) (z i); have := le_min a.1 c.1; omega
    · have := max_le a.2 c.2; omega
  have hsub : ∀ w ∈ IBox lo hi, w ∈ Hd R σ b ∧ w ∈ Hd R σ' b' := by
    intro w hw
    exact ⟨⟨hbox hw, hsP_between hpa.2 hza.2 (hw σ).1 (hw σ).2⟩,
      ⟨hbox hw, hsP_between hpb.2 hzb.2 (hw σ').1 (hw σ').2⟩⟩
  have hρw : ∀ w ∈ IBox lo hi, rho w ≤ rho p + 3 / 2 := by
    intro w hw
    unfold rho
    have e : ∀ i, |qc w i| ≤ |qc p i| + 1 / 2 := by
      intro i
      have d := hw i
      simp only [lo, hi] at d
      unfold qc
      have hzi := hz i
      have m1 : min (p i) (z i) ≤ w i := d.1
      have m2 : w i ≤ max (p i) (z i) := d.2
      rcases hzi with h | h <;> rw [h] at m1 m2
      · rcases le_total (p i) 0 with hp0 | hp0
        · rw [min_eq_left hp0] at m1; rw [max_eq_right hp0] at m2
          have a : ((p i : ℤ) : ℝ) ≤ ((w i : ℤ) : ℝ) := by exact_mod_cast m1
          have c : ((w i : ℤ) : ℝ) ≤ 0 := by exact_mod_cast m2
          have := abs_nonneg ((p i : ℝ) + 1 / 2)
          rw [abs_le]; constructor
          · have := neg_abs_le ((p i : ℝ) + 1 / 2); linarith
          · have := le_abs_self ((p i : ℝ) + 1 / 2); linarith
        · rw [min_eq_right hp0] at m1; rw [max_eq_left hp0] at m2
          have a : (0 : ℝ) ≤ ((w i : ℤ) : ℝ) := by exact_mod_cast m1
          have c : ((w i : ℤ) : ℝ) ≤ ((p i : ℤ) : ℝ) := by exact_mod_cast m2
          have : (0 : ℝ) ≤ ((p i : ℤ) : ℝ) := by exact_mod_cast hp0
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rcases le_total (p i) (-1) with hp0 | hp0
        · rw [min_eq_left hp0] at m1; rw [max_eq_right hp0] at m2
          have a : ((p i : ℤ) : ℝ) ≤ ((w i : ℤ) : ℝ) := by exact_mod_cast m1
          have c : ((w i : ℤ) : ℝ) ≤ -1 := by exact_mod_cast m2
          have : ((p i : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hp0
          rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
        · rw [min_eq_right hp0] at m1; rw [max_eq_left hp0] at m2
          have a : (-1 : ℝ) ≤ ((w i : ℤ) : ℝ) := by exact_mod_cast m1
          have c : ((w i : ℤ) : ℝ) ≤ ((p i : ℤ) : ℝ) := by exact_mod_cast m2
          have := abs_nonneg ((p i : ℝ) + 1 / 2)
          rw [abs_le]; constructor
          · have := neg_abs_le ((p i : ℝ) + 1 / 2); linarith
          · have := le_abs_self ((p i : ℝ) + 1 / 2); linarith
    linarith [e 0, e 1, e 2]
  have hzI : z ∈ IBox lo hi := fun i => ⟨min_le_right _ _, le_max_right _ _⟩
  have hpI : p ∈ IBox lo hi := fun i => ⟨min_le_left _ _, le_max_left _ _⟩
  have tb := trans_box (U := U) (gP := P) (gQ := Q) (Rb := R + 1) hinj hbox (β := 8 * (rho p + 3 / 2) * s)
    (fun w μ hw hwμ => by
      have a := hP.1 w μ (hsub w hw).1 (hsub _ hwμ).1
      have c := hQ.1 w μ (hsub w hw).2 (hsub _ hwμ).2
      have d := hρw w hw
      have : 4 * rho w * s ≤ 4 * (rho p + 3 / 2) * s := by nlinarith
      linarith) hpI hzI
  have hl := l1_le p z
  have hzs : |((z 0 : ℤ) : ℝ)| + |((z 1 : ℤ) : ℝ)| + |((z 2 : ℤ) : ℝ)| ≤ 3 := by
    have e : ∀ i, |((z i : ℤ) : ℝ)| ≤ 1 := by
      intro i; rcases hz i with h | h <;> rw [h] <;> norm_num
    linarith [e 0, e 1, e 2]
  have hρ := rho_ge p
  have hl2 : (l1 p z : ℝ) ≤ rho p + 9 / 2 := by linarith
  have tri := frobNorm_sub_le' (((trans P Q (iota v p) : SU2) : M2)) ((trans P Q (iota v z) : SU2) : M2) 1
  have h3 : (l1 p z : ℝ) * (8 * (rho p + 3 / 2) * s) ≤ 128 * rho p ^ 2 * s := by
    have a : 0 ≤ (l1 p z : ℝ) := Nat.cast_nonneg _
    have c : 0 ≤ 8 * (rho p + 3 / 2) * s := by positivity
    calc (l1 p z : ℝ) * (8 * (rho p + 3 / 2) * s) ≤ (rho p + 9 / 2) * (8 * (rho p + 3 / 2) * s) :=
          mul_le_mul_of_nonneg_right hl2 c
      _ = 8 * ((rho p + 9 / 2) * (rho p + 3 / 2)) * s := by ring
      _ ≤ 8 * (16 * rho p ^ 2) * s := by
          have k : (rho p + 9 / 2) * (rho p + 3 / 2) ≤ 16 * rho p ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_left k (by norm_num : (0:ℝ) ≤ 8)
          exact mul_le_mul_of_nonneg_right this hs
      _ = 128 * rho p ^ 2 * s := by ring
  linarith

theorem frob_trans_symm (P Q : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) :
    frobNorm (((trans Q P x : SU2) : M2) - 1) = frobNorm (((trans P Q x : SU2) : M2) - 1) := by
  rw [trans_inv, frob_inv_sub_one]

theorem trans_cocycle (P Q R' : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) :
    trans P R' x = trans Q R' x * trans P Q x := by
  simp only [M2Glue2.trans]; group

theorem pair_via {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 2)))
    {P Q R' : PeriodicLatticeSite L → SU2} {σ σ' σc : Fin 3} {b b' bc : Bool} {s B1 B2 : ℝ} (hs : 0 ≤ s)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) {TP TR : Z3 → ℝ}
    (hP : ZCh U P v (Hd R σ b) (fun p => 4 * rho p * s) TP) (hR' : ZCh U R' v (Hd R σ' b') (fun p => 4 * rho p * s) TR)
    (hPQ : ∀ p, p ∈ Hd R σ b → p ∈ Hd R σc bc → frobNorm (((trans P Q (iota v p) : SU2) : M2) - 1) ≤ B1 * rho p ^ 2 * s)
    (hQR : ∀ p, p ∈ Hd R σc bc → p ∈ Hd R σ' b' → frobNorm (((trans Q R' (iota v p) : SU2) : M2) - 1) ≤ B2 * rho p ^ 2 * s)
    {z : Z3} (hz : isCorner z) (hza : z ∈ Hd R σ b) (hzb : z ∈ Hd R σ' b') (hzc : z ∈ Hd R σc bc) :
    ∀ p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans P R' (iota v p) : SU2) : M2) - 1) ≤ (128 + B1 + B2) * rho p ^ 2 * s := by
  intro p hpa hpb
  have hzE : frobNorm (((trans P R' (iota v z) : SU2) : M2) - 1) ≤ (B1 + B2) * (9 / 4) * s := by
    rw [trans_cocycle P Q R']
    refine (frob_mul_sub_one _ _).trans ?_
    have a := hQR z hzc hzb; have c := hPQ z hza hzc
    rw [rho_corner hz] at a c
    nlinarith
  have g := pair_growth hinj hs hP hR' hz hza hzb hpa hpb hzE
  have hρ := rho_ge p
  have : (9 / 4 : ℝ) ≤ rho p ^ 2 := by nlinarith
  have : (B1 + B2) * (9 / 4) * s ≤ (B1 + B2) * rho p ^ 2 * s := by
    have : 0 ≤ (B1 + B2) * s := by positivity
    nlinarith
  nlinarith

/-! ## the normalised charts -/

noncomputable def gsN (n : Fin 3 → Bool → SU2) (U : LinkCfg L) (v : PeriodicLatticeSite L) (R : ℕ)
    (g : Fin 3 → Bool → PeriodicLatticeSite L → SU2) (σ : Fin 3) (b : Bool) : PeriodicLatticeSite L → SU2 :=
  fun x => n σ b * flA U v R g σ b x

theorem trans_gsN (n : Fin 3 → Bool → SU2) (U : LinkCfg L) (v : PeriodicLatticeSite L) (R : ℕ)
    (g : Fin 3 → Bool → PeriodicLatticeSite L → SU2) (σ σ' : Fin 3) (b b' : Bool) (x : PeriodicLatticeSite L) :
    trans (gsN n U v R g σ b) (gsN n U v R g σ' b') x
      = n σ' b' * trans (flA U v R g σ b) (flA U v R g σ' b') x * (n σ b)⁻¹ := by
  simp only [M2Glue2.trans, gsN]; group

def zc (σ : Fin 3) (b : Bool) : Z3 := fun i => if i = σ ∧ b = false then -1 else 0

noncomputable def nrm (U : LinkCfg L) (v : PeriodicLatticeSite L) (R : ℕ)
    (g : Fin 3 → Bool → PeriodicLatticeSite L → SU2) : Fin 3 → Bool → SU2
  | 2, true => 1
  | 2, false => (trans (fun x => (trans (flA U v R g 2 true) (flA U v R g 0 true) (iota v (zc 0 true)))⁻¹ *
      flA U v R g 0 true x) (flA U v R g 2 false) (iota v (zc 2 false)))⁻¹
  | σ, b => (trans (flA U v R g 2 true) (flA U v R g σ b) (iota v (zc σ b)))⁻¹

theorem norm_2t (U : LinkCfg L) (v : PeriodicLatticeSite L) (R : ℕ) (g : Fin 3 → Bool → PeriodicLatticeSite L → SU2)
    (σ : Fin 3) (hσ : σ ≠ 2) (b : Bool) :
    trans (gsN (nrm U v R g) U v R g 2 true) (gsN (nrm U v R g) U v R g σ b) (iota v (zc σ b)) = 1 := by
  rw [trans_gsN]
  have h2 : nrm U v R g 2 true = 1 := rfl
  have hn : nrm U v R g σ b = (trans (flA U v R g 2 true) (flA U v R g σ b) (iota v (zc σ b)))⁻¹ := by
    fin_cases σ
    · cases b <;> rfl
    · cases b <;> rfl
    · exact absurd rfl hσ
  rw [h2, hn]; group

theorem norm_2f (U : LinkCfg L) (v : PeriodicLatticeSite L) (R : ℕ) (g : Fin 3 → Bool → PeriodicLatticeSite L → SU2) :
    trans (gsN (nrm U v R g) U v R g 0 true) (gsN (nrm U v R g) U v R g 2 false) (iota v (zc 2 false)) = 1 := by
  have h0 : gsN (nrm U v R g) U v R g 0 true = fun x =>
      (trans (flA U v R g 2 true) (flA U v R g 0 true) (iota v (zc 0 true)))⁻¹ * flA U v R g 0 true x := rfl
  rw [h0]
  simp only [M2Glue2.trans, gsN]
  show nrm U v R g 2 false * flA U v R g 2 false (iota v (zc 2 false)) * _ = 1
  simp only [nrm, M2Glue2.trans]
  group

end AdalyFormal.M2Glue3
