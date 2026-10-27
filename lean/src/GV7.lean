import GV6

/-!
# GV7 -- the far field: margin sets, local chart bounds along the sequence, coverage (m2_glue3, 2026-10-15)

* `Fseq`: far sets (`ρ ≥ 32`) carrying glue_two's trichotomy by construction (radius-2 margins).
* `zch_seq`: `Aseq j` is a coordinate chart on `Fseq j` with bounds `cA j · ρ · s`, `cC j · s`.
* `Fseq_cover`: every point of `Box R` with `ρ ≥ 600` lies in `Fseq 5`.
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
open AdalyFormal.Balaban.Bch2 (frobNorm_nonneg)

variable {L : PeriodicLatticeExtent}

def nb (R : ℕ) (p : Z3) : Set Z3 := {p' | p' ∈ Box R ∧ ∀ i, |p' i - p i| ≤ 2}

def Fseq (R : ℕ) : ℕ → Set Z3
  | 0 => {p | p ∈ Box R ∧ 32 ≤ rho p ∧ hsP (ordA 0).1 (ordA 0).2 p}
  | j + 1 => {p | p ∈ Box R ∧ 32 ≤ rho p ∧ ((∃ p' ∈ nb R p, Cj (j + 1) p' < 1) → nb R p ⊆ Fseq R j) ∧
      ((∃ p' ∈ nb R p, 0 < Cj (j + 1) p') → ∀ p' ∈ nb R p, hsP (ordA (j + 1)).1 (ordA (j + 1)).2 p')}

theorem Fseq_box (R j : ℕ) : Fseq R j ⊆ Box R := by
  cases j with
  | zero => exact fun _ h => h.1
  | succ j => exact fun _ h => h.1

theorem Fseq_far (R j : ℕ) {p : Z3} (h : p ∈ Fseq R j) : 32 ≤ rho p := by
  cases j with
  | zero => exact h.2.1
  | succ j => exact h.2.1

theorem self_mem_nb {R : ℕ} {p : Z3} (hp : p ∈ Box R) : p ∈ nb R p := ⟨hp, fun i => by simp⟩

theorem Fseq_sub_Useq (R : ℕ) : ∀ j, Fseq R j ⊆ Useq R j := by
  intro j
  induction j with
  | zero => exact fun p h => ⟨h.1, h.2.2⟩
  | succ j ih =>
    intro p h
    refine ⟨h.1, fun hlt => ?_⟩
    exact ih (h.2.2.1 ⟨p, self_mem_nb h.1, hlt⟩ (self_mem_nb h.1))

/-! ## constants -/

noncomputable def cG (A B : ℝ) : ℝ := 8 * K1 * B + 8 * A

noncomputable def cA (A0 B0 : ℝ) : ℕ → ℝ
  | 0 => A0
  | j + 1 => 38 * cA A0 B0 j + 36 * K1 * cB B0 j

noncomputable def cC (A0 B0 : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => 19 * cC A0 B0 j + 72 * K2 * cB B0 j + 144 * K1 * cA A0 B0 j
      + 18 * cA A0 B0 j * cG (cA A0 B0 j) (cB B0 j) + 504 * cA A0 B0 j ^ 2
      + (135 / 4) * cG (cA A0 B0 j) (cB B0 j) ^ 2

theorem cB_nonneg {B0 : ℝ} (h : 0 ≤ B0) (j : ℕ) : 0 ≤ cB B0 j := by unfold cB; positivity

theorem cA_ge {A0 B0 : ℝ} (hA : 0 ≤ A0) (hB : 0 ≤ B0) : ∀ j, A0 ≤ cA A0 B0 j := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    show A0 ≤ 38 * cA A0 B0 j + 36 * K1 * cB B0 j
    have := cB_nonneg hB j; have := K1_pos
    nlinarith

theorem cC_ge {A0 B0 : ℝ} (hA : 0 ≤ A0) (hB : 0 ≤ B0) : ∀ j, 1 ≤ cC A0 B0 j := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    show 1 ≤ 19 * cC A0 B0 j + 72 * K2 * cB B0 j + 144 * K1 * cA A0 B0 j
      + 18 * cA A0 B0 j * cG (cA A0 B0 j) (cB B0 j) + 504 * cA A0 B0 j ^ 2
      + (135 / 4) * cG (cA A0 B0 j) (cB B0 j) ^ 2
    have a := (cA_ge hA hB j)
    have b := cB_nonneg hB j
    have k1 := K1_pos; have k2 := K2_pos
    have hG : 0 ≤ cG (cA A0 B0 j) (cB B0 j) := by unfold cG; nlinarith
    have : 0 ≤ cA A0 B0 j := hA.trans a
    nlinarith [sq_nonneg (cA A0 B0 j), sq_nonneg (cG (cA A0 B0 j) (cB B0 j)), mul_nonneg this hG,
      mul_nonneg k2.le b, mul_nonneg k1.le this]

theorem gT1_eq (A B ρ s : ℝ) (hρ : 0 < ρ) :
    glueT1 (2 * A * ρ * s) (4 * B * ρ ^ 2 * s) (2 * K1 / ρ) = (38 * A + 36 * K1 * B) * ρ * s := by
  unfold glueT1 glueK; field_simp; ring

theorem gT2_le {A B C ρ s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hw : ρ ^ 2 * s ≤ 1) :
    glueT2 (2 * A * ρ * s) (C * s) (4 * B * ρ ^ 2 * s) (2 * K1 / ρ) (4 * K2 / ρ ^ 2)
      ≤ (19 * C + 72 * K2 * B + 144 * K1 * A + 18 * A * cG A B + 504 * A ^ 2 + (135 / 4) * cG A B ^ 2) * s := by
  have e : glueT2 (2 * A * ρ * s) (C * s) (4 * B * ρ ^ 2 * s) (2 * K1 / ρ) (4 * K2 / ρ ^ 2)
      = (19 * C + 72 * K2 * B + 144 * K1 * A) * s
        + (ρ ^ 2 * s) * s * (18 * A * cG A B + 504 * A ^ 2 + (135 / 4) * cG A B ^ 2) := by
    unfold glueT2 glueK cG; field_simp; ring
  rw [e]
  have hG : 0 ≤ cG A B := by unfold cG; have := K1_pos; positivity
  have hX : 0 ≤ 18 * A * cG A B + 504 * A ^ 2 + (135 / 4) * cG A B ^ 2 := by positivity
  have : (ρ ^ 2 * s) * s * (18 * A * cG A B + 504 * A ^ 2 + (135 / 4) * cG A B ^ 2)
      ≤ 1 * s * (18 * A * cG A B + 504 * A ^ 2 + (135 / 4) * cG A B ^ 2) := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw hs) hX
  nlinarith

/-! ## window comparability of `ρ` -/

theorem qc_dist {p p' : Z3} {k : ℤ} (h : ∀ i, |p' i - p i| ≤ k) : ∀ i, |qc p' i - qc p i| ≤ (k : ℝ) := by
  intro i
  have : qc p' i - qc p i = ((p' i - p i : ℤ) : ℝ) := by unfold qc; push_cast; ring
  rw [this]
  have := h i
  rw [← Int.cast_abs]; exact_mod_cast this

theorem rho_win {p p' : Z3} (h : ∀ i, |p' i - p i| ≤ 2) (hρ : 12 ≤ rho p) :
    rho p / 2 ≤ rho p' ∧ rho p' ≤ 2 * rho p := by
  have := rho_perturb (qc_dist h)
  push_cast at this
  constructor <;> linarith [this.1, this.2]

/-! ## the local chart along the sequence -/

theorem zch_seq {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 2)))
    {gs : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {A0 B0 s : ℝ} (hA0 : 0 ≤ A0) (hB0 : 0 ≤ B0) (hs0 : 0 ≤ s)
    (hZ : ∀ σ b, ZCh U (gs σ b) v (Hd R σ b) (fun p => A0 * rho p * s) (fun _ => s))
    (hpair : ∀ σ b σ' b' p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (gs σ b) (gs σ' b') (iota v p) : SU2) : M2) - 1) ≤ B0 * rho p ^ 2 * s)
    (hsmall : ∀ p ∈ Box R, (4 * cB B0 5 + 1) * rho p ^ 2 * s ≤ 1) :
    ∀ j, j ≤ 5 → ZCh U (Aseq v R gs j) v (Fseq R j) (fun p => cA A0 B0 j * rho p * s)
      (fun _ => cC A0 B0 j * s) := by
  have hinj1 : Set.InjOn (iota v) (Box (R + 1)) := hinj.mono (Box_mono (Nat.le_succ _))
  have hw : ∀ p ∈ Box R, rho p ^ 2 * s ≤ 1 := by
    intro p hp; have := hsmall p hp; have := cB_nonneg hB0 5
    have : 0 ≤ rho p ^ 2 * s := by positivity
    nlinarith
  have hcl := close_seq (U := U) hinj1 hB0 hs0 hpair (fun p hp => by
    have := hsmall p hp; have := cB_nonneg hB0 5
    have : 0 ≤ rho p ^ 2 * s := by positivity
    nlinarith)
  intro j
  induction j with
  | zero =>
    intro _
    refine (hZ (ordA 0).1 (ordA 0).2).mono (fun p hp => ⟨Box_mono (Nat.le_succ R) hp.1, hp.2.2⟩)
      (fun p _ => le_rfl) (fun p _ => ?_)
    simp [cC]
  | succ j ih =>
    intro hj
    have IH := ih (by omega)
    have cAj := cA_ge hA0 hB0 j
    have cCj := cC_ge hA0 hB0 j
    have cBj := cB_nonneg hB0 j
    have cBj5 : cB B0 j ≤ cB B0 5 := cB_mono hB0 (by omega)
    set b := ordA (j + 1)
    have hSP : Fseq R j ⊆ Box (R + 1) := (Fseq_box R j).trans (Box_mono (Nat.le_succ R))
    have hSQ : Hd R b.1 b.2 ⊆ Box (R + 1) := fun p hp => hp.1
    have hSD : Fseq R (j + 1) ⊆ Box (R + 1) := (Fseq_box R (j + 1)).trans (Box_mono (Nat.le_succ R))
    have hQ : ZCh U (gs b.1 b.2) v (Hd R b.1 b.2) (fun p => cA A0 B0 j * rho p * s) (fun _ => cC A0 B0 j * s) :=
      (hZ b.1 b.2).mono le_rfl (fun p _ => by
          have := rho_pos p
          show A0 * rho p * s ≤ cA A0 B0 j * rho p * s
          have : 0 ≤ rho p * s := by positivity
          nlinarith)
        (fun p _ => by show s ≤ cC A0 B0 j * s; nlinarith)
    have key := glue_zstep (U := U) (Rb := R + 1) hinj hSP hSQ hSD
      (C := Cj (j + 1)) (c := cs v R (j + 1)) (fun p hp => cs_iota hinj1 (j + 1) hp)
      (T1 := fun p => cA A0 B0 j * rho p * s) (T2 := fun _ => cC A0 B0 j * s)
      (τ := fun p => cB B0 j * rho p ^ 2 * s) (k1 := fun p => K1 / rho p) (k2 := fun p => K2 / rho p ^ 2)
      (W1 := fun p => 2 * cA A0 B0 j * rho p * s) (W2 := fun _ => cC A0 B0 j * s)
      (Wτ := fun p => 4 * cB B0 j * rho p ^ 2 * s) (Wk1 := fun p => 2 * K1 / rho p)
      (Wk2 := fun p => 4 * K2 / rho p ^ 2) IH hQ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · refine key.mono le_rfl (fun p hp => ?_) (fun p hp => ?_)
      · have hρ : 0 < rho p := rho_pos p
        show glueT1 (2 * cA A0 B0 j * rho p * s) (4 * cB B0 j * rho p ^ 2 * s) (2 * K1 / rho p)
          ≤ cA A0 B0 (j + 1) * rho p * s
        rw [gT1_eq _ _ _ _ hρ]; rfl
      · have hρ : 0 < rho p := rho_pos p
        show glueT2 (2 * cA A0 B0 j * rho p * s) (cC A0 B0 j * s) (4 * cB B0 j * rho p ^ 2 * s)
          (2 * K1 / rho p) (4 * K2 / rho p ^ 2) ≤ cC A0 B0 (j + 1) * s
        exact gT2_le (hA0.trans cAj) cBj hs0 hρ (hw p (Fseq_box R _ hp))
    · -- transitions
      intro p hpP hpQ
      rw [trans_inv, frob_inv_sub_one]
      exact hcl j (by omega) p (Fseq_sub_Useq R j hpP) b.1 b.2 hpQ
    · exact fun p _ => Cj_mem _ _
    · intro p ν hp _
      exact capC_bond _ _ p ν (by linarith [Fseq_far R _ hp])
    · intro p μ ν hp _ _ _
      exact capC_sten _ _ p μ ν (by linarith [Fseq_far R _ hp])
    · -- bond trichotomy
      intro p ν hp hpν
      obtain ⟨hpB, _, h1, h2⟩ := hp
      have m0 : p ∈ nb R p := self_mem_nb hpB
      have m1 : p + ev ν ∈ nb R p := ⟨Fseq_box R _ hpν, fun i => by
        have := ev_abs ν i; simp only [Pi.add_apply, add_sub_cancel_left]; linarith⟩
      by_cases hall : Cj (j + 1) p = 1 ∧ Cj (j + 1) (p + ev ν) = 1
      · right; left
        refine ⟨hall.1, hall.2, ⟨Box_mono (Nat.le_succ R) hpB, hs_of_capC_pos (by
          show 0 < Cj (j + 1) p; rw [hall.1]; norm_num)⟩,
          ⟨Box_mono (Nat.le_succ R) (Fseq_box R _ hpν), hs_of_capC_pos (by
          show 0 < Cj (j + 1) (p + ev ν); rw [hall.2]; norm_num)⟩⟩
      · have hlt : ∃ p' ∈ nb R p, Cj (j + 1) p' < 1 := by
          by_cases a : Cj (j + 1) p = 1
          · exact ⟨_, m1, lt_of_le_of_ne (Cj_mem _ _).2 (fun e => hall ⟨a, e⟩)⟩
          · exact ⟨_, m0, lt_of_le_of_ne (Cj_mem _ _).2 a⟩
        have hF := h1 hlt
        by_cases hz : Cj (j + 1) p = 0 ∧ Cj (j + 1) (p + ev ν) = 0
        · left; exact ⟨hz.1, hz.2, hF m0, hF m1⟩
        · right; right
          have hpos : ∃ p' ∈ nb R p, 0 < Cj (j + 1) p' := by
            by_cases a : Cj (j + 1) p = 0
            · exact ⟨_, m1, lt_of_le_of_ne (Cj_mem _ _).1 (fun e => hz ⟨a, e.symm⟩)⟩
            · exact ⟨_, m0, lt_of_le_of_ne (Cj_mem _ _).1 (Ne.symm a)⟩
          have hH := h2 hpos
          exact ⟨hF m0, ⟨Box_mono (Nat.le_succ R) m0.1, hH _ m0⟩, hF m1,
            ⟨Box_mono (Nat.le_succ R) m1.1, hH _ m1⟩⟩
    · -- stencil trichotomy
      intro p μ ν hp hpν hpμ hpμν
      obtain ⟨hpB, _, h1, h2⟩ := hp
      have mem : ∀ y ∈ ({p, p + ev ν, p + ev μ, p + ev μ + ev ν} : Set Z3), y ∈ nb R p := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact self_mem_nb hpB
        · exact ⟨Fseq_box R _ hpν, fun i => by
            have := ev_abs ν i; simp only [Pi.add_apply, add_sub_cancel_left]; linarith⟩
        · exact ⟨Fseq_box R _ hpμ, fun i => by
            have := ev_abs μ i; simp only [Pi.add_apply, add_sub_cancel_left]; linarith⟩
        · exact ⟨Fseq_box R _ hpμν, (ev2_mem_win (S := Set.univ) (p := p) (μ := μ) (ν := ν) trivial).2⟩
      by_cases hall : ∀ y ∈ ({p, p + ev ν, p + ev μ, p + ev μ + ev ν} : Set Z3), Cj (j + 1) y = 1
      · right; left
        intro y hy
        refine ⟨hall y hy, Box_mono (Nat.le_succ R) (mem y hy).1, hs_of_capC_pos (by
          show 0 < Cj (j + 1) y; rw [hall y hy]; norm_num)⟩
      · push Not at hall
        obtain ⟨y0, hy0, hy0'⟩ := hall
        have hF := h1 ⟨y0, mem y0 hy0, lt_of_le_of_ne (Cj_mem _ _).2 hy0'⟩
        by_cases hz : ∀ y ∈ ({p, p + ev ν, p + ev μ, p + ev μ + ev ν} : Set Z3), Cj (j + 1) y = 0
        · left; intro y hy; exact ⟨hz y hy, hF (mem y hy)⟩
        · right; right
          push Not at hz
          obtain ⟨y1, hy1, hy1'⟩ := hz
          have hH := h2 ⟨y1, mem y1 hy1, lt_of_le_of_ne (Cj_mem _ _).1 (Ne.symm hy1')⟩
          intro y hy
          exact ⟨hF (mem y hy), Box_mono (Nat.le_succ R) (mem y hy).1, hH y (mem y hy)⟩
    · -- window bounds
      intro p p' hp hp'
      have hρ := Fseq_far R _ hp
      obtain ⟨r1, r2⟩ := rho_win hp'.2 (by linarith)
      have hρ0 : 0 < rho p := by linarith
      have hρ0' : 0 < rho p' := by linarith
      refine ⟨?_, le_rfl, ?_, ?_, ?_⟩
      · show cA A0 B0 j * rho p' * s ≤ 2 * cA A0 B0 j * rho p * s
        have : 0 ≤ cA A0 B0 j * s := mul_nonneg (hA0.trans cAj) hs0
        nlinarith
      · show cB B0 j * rho p' ^ 2 * s ≤ 4 * cB B0 j * rho p ^ 2 * s
        have h2 : rho p' ^ 2 ≤ 4 * rho p ^ 2 := by nlinarith
        have : 0 ≤ cB B0 j * s := mul_nonneg cBj hs0
        nlinarith
      · show K1 / rho p' ≤ 2 * K1 / rho p
        rw [div_le_div_iff₀ hρ0' hρ0]; have := K1_pos; nlinarith
      · show K2 / rho p' ^ 2 ≤ 4 * K2 / rho p ^ 2
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : rho p ^ 2 ≤ 4 * rho p' ^ 2 := by nlinarith
        have := K2_pos; nlinarith
    · -- nonnegativity
      intro p hp
      have hρ0 : 0 < rho p := by linarith [Fseq_far R _ hp]
      have hpB := Fseq_box R _ hp
      refine ⟨by have := hA0.trans cAj; positivity, by positivity, by positivity, ?_,
        by have := K1_pos; positivity, by have := K2_pos; positivity⟩
      have := hsmall p hpB
      have : 0 ≤ rho p ^ 2 * s := by positivity
      nlinarith

end AdalyFormal.M2Glue3
