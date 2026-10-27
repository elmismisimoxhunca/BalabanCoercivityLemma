import GV5

/-!
# GV6 -- the cap sequence: definitions, pointwise closeness, coverage of the ball (m2_glue3, 2026-10-15)

Prepared charts `gs σ b` (one per half-space `hsP σ b`) are glued in the order
`(2,+), (0,+), (1,+), (0,−), (1,−), (2,−)` with the caps `Cj j = capC (ordA j)`:
`Aseq 0 = gs (2,+)`, `Aseq (j+1) = gglue (Aseq j) (gs (ordA (j+1))) (Cj (j+1) ∘ coord)`.
* `Useq`: pointwise domains; `close_seq`: `|Aseq j · (gs a)⁻¹ − 1| ≤ (11/2)^j B₀ ρ² s` on `Useq j ∩ H_a`.
* `Useq_five`: `Useq 5 = Box R` (every point has a cap with value `1`).
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

/-! ## group-level helpers -/

theorem frob_inv_sub_one (h : SU2) : frobNorm (((h⁻¹ : SU2) : M2) - 1) = frobNorm ((h : M2) - 1) := by
  rw [coe_inv]; exact frobNorm_star_sub_one h

theorem frob_mul_sub_one (k T : SU2) :
    frobNorm (((k * T : SU2) : M2) - 1) ≤ frobNorm ((k : M2) - 1) + frobNorm ((T : M2) - 1) := by
  rw [coe_mul]
  have e : (k : M2) * (T : M2) - 1 = (k : M2) * ((T : M2) - 1) + ((k : M2) - 1) := by noncomm_ring
  rw [e]
  refine (frobNorm_add_le _ _).trans ?_
  rw [frobNorm_su2_mul]; linarith

theorem trans_inv (gP gQ : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) :
    trans gQ gP x = (trans gP gQ x)⁻¹ := by
  simp only [M2Glue2.trans]; group

/-- one closeness step at a point. -/
theorem close_step {A G Ga : SU2} {c β : ℝ} (hc : 0 ≤ c ∧ c ≤ 1)
    (hT : frobNorm (((A * Ga⁻¹ : SU2) : M2) - 1) ≤ β) (hh : frobNorm (((A * G⁻¹ : SU2) : M2) - 1) ≤ β)
    (hβ : β ≤ 2) :
    frobNorm (((cay (c • icay (G * A⁻¹)) * A * Ga⁻¹ : SU2) : M2) - 1) ≤ (11 / 2) * β := by
  have hh' : frobNorm (((G * A⁻¹ : SU2) : M2) - 1) ≤ β := by
    rw [show G * A⁻¹ = (A * G⁻¹)⁻¹ by group, frob_inv_sub_one]; exact hh
  have hk : frobNorm (((cay (c • icay (G * A⁻¹)) : SU2) : M2) - 1) ≤ (9 / 2) * β := by
    refine (frobNorm_cay_sub_one_le ((isSu2_icay _).smul c)).trans ?_
    rw [frobNorm_smul]
    have hi := frobNorm_icay_le (hh'.trans hβ)
    have ha : |c| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2
    have : |c| * frobNorm (icay (G * A⁻¹)) ≤ 1 * β :=
      mul_le_mul ha (hi.trans hh') (frobNorm_nonneg _) (by norm_num)
    linarith
  rw [mul_assoc]
  refine (frob_mul_sub_one _ _).trans ?_
  linarith

/-! ## the sequence -/

def ordA : ℕ → Fin 3 × Bool
  | 0 => (2, true)
  | 1 => (0, true)
  | 2 => (1, true)
  | 3 => (0, false)
  | 4 => (1, false)
  | _ => (2, false)

def idxA : Fin 3 → Bool → ℕ
  | 2, true => 0
  | 0, true => 1
  | 1, true => 2
  | 0, false => 3
  | 1, false => 4
  | 2, false => 5

theorem ordA_idxA (σ : Fin 3) (b : Bool) : ordA (idxA σ b) = (σ, b) := by
  fin_cases σ <;> cases b <;> rfl

theorem idxA_le (σ : Fin 3) (b : Bool) : idxA σ b ≤ 5 := by
  fin_cases σ <;> cases b <;> decide

noncomputable def Cj (j : ℕ) (p : Z3) : ℝ := capC (ordA j).1 (ordA j).2 p

/-- the chart domain of a prepared half-space chart. -/
def Hd (R : ℕ) (σ : Fin 3) (b : Bool) : Set Z3 := {p | p ∈ Box (R + 1) ∧ hsP σ b p}

noncomputable def cs (v : PeriodicLatticeSite L) (R : ℕ) (j : ℕ) (x : PeriodicLatticeSite L) : ℝ :=
  Cj j (coord v (R + 1) x)

noncomputable def Aseq (v : PeriodicLatticeSite L) (R : ℕ) (gs : Fin 3 → Bool → PeriodicLatticeSite L → SU2) :
    ℕ → PeriodicLatticeSite L → SU2
  | 0 => gs (ordA 0).1 (ordA 0).2
  | j + 1 => gglue (Aseq v R gs j) (gs (ordA (j + 1)).1 (ordA (j + 1)).2) (cs v R (j + 1))

def Useq (R : ℕ) : ℕ → Set Z3
  | 0 => {p | p ∈ Box R ∧ hsP (ordA 0).1 (ordA 0).2 p}
  | j + 1 => {p | p ∈ Box R ∧ (Cj (j + 1) p < 1 → p ∈ Useq R j)}

noncomputable def cB (B0 : ℝ) (j : ℕ) : ℝ := (11 / 2) ^ j * B0

theorem cB_succ (B0 : ℝ) (j : ℕ) : cB B0 (j + 1) = (11 / 2) * cB B0 j := by
  unfold cB; rw [pow_succ]; ring

theorem cB_mono {B0 : ℝ} (hB : 0 ≤ B0) {i j : ℕ} (h : i ≤ j) : cB B0 i ≤ cB B0 j := by
  unfold cB
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) hB

theorem Useq_sub (R j : ℕ) : Useq R j ⊆ Box R := by
  cases j with
  | zero => exact fun _ h => h.1
  | succ j => exact fun _ h => h.1

theorem Useq_mono (R j : ℕ) : Useq R j ⊆ Useq R (j + 1) := fun p hp =>
  ⟨Useq_sub R j hp, fun _ => hp⟩

theorem cs_iota {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 1))) (j : ℕ)
    {p : Z3} (hp : p ∈ Box (R + 1)) : cs v R j (iota v p) = Cj j p := by
  unfold cs; rw [coord_iota hinj hp]

theorem Cj_mem (j : ℕ) (p : Z3) : 0 ≤ Cj j p ∧ Cj j p ≤ 1 := capC_mem _ _ _

/-- pointwise closeness of the sequence to every prepared chart. -/
theorem close_seq {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 1)))
    {gs : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {B0 s : ℝ} (hB0 : 0 ≤ B0) (hs0 : 0 ≤ s)
    (hpair : ∀ σ b σ' b' p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (gs σ b) (gs σ' b') (iota v p) : SU2) : M2) - 1) ≤ B0 * rho p ^ 2 * s)
    (hsm : ∀ p ∈ Box R, cB B0 5 * rho p ^ 2 * s ≤ 2) :
    ∀ j, j ≤ 5 → ∀ p ∈ Useq R j, ∀ σ b, p ∈ Hd R σ b →
      frobNorm (((trans (gs σ b) (Aseq v R gs j) (iota v p) : SU2) : M2) - 1) ≤ cB B0 j * rho p ^ 2 * s := by
  have _ := U
  intro j
  induction j with
  | zero =>
    intro _ p hp σ b hpa
    have h0 : p ∈ Hd R (ordA 0).1 (ordA 0).2 := ⟨Box_mono (Nat.le_succ R) hp.1, hp.2⟩
    have := hpair σ b _ _ p hpa h0
    simpa [Aseq, cB] using this
  | succ j ih =>
    intro hj p hp σ b hpa
    have hpB : p ∈ Box R := hp.1
    have hpB1 : p ∈ Box (R + 1) := Box_mono (Nat.le_succ R) hpB
    have hcB := cB_succ B0 j
    have hsm' : cB B0 j * rho p ^ 2 * s ≤ 2 := by
      have := hsm p hpB
      have m := cB_mono hB0 (show j ≤ 5 by omega)
      by_cases hs : 0 ≤ rho p ^ 2 * s
      · calc cB B0 j * rho p ^ 2 * s = cB B0 j * (rho p ^ 2 * s) := by ring
          _ ≤ cB B0 5 * (rho p ^ 2 * s) := mul_le_mul_of_nonneg_right m hs
          _ = cB B0 5 * rho p ^ 2 * s := by ring
          _ ≤ 2 := this
      · push Not at hs
        have : 0 ≤ cB B0 j := by unfold cB; positivity
        nlinarith
    have hc := cs_iota (L := L) hinj (j + 1) hpB1 (v := v)
    -- the new gauge at `iota v p`
    have hA : Aseq v R gs (j + 1) (iota v p) = gglue (Aseq v R gs j) (gs (ordA (j + 1)).1 (ordA (j + 1)).2)
        (cs v R (j + 1)) (iota v p) := rfl
    rcases eq_or_lt_of_le (Cj_mem (j + 1) p).2 with h1 | h1
    · -- cap value 1: the new gauge is the chart `ordA (j+1)` itself
      have hc1 : cs v R (j + 1) (iota v p) = 1 := by rw [hc, h1]
      have hs : hsP (ordA (j + 1)).1 (ordA (j + 1)).2 p := hs_of_capC_pos (by
        show 0 < Cj (j + 1) p; rw [h1]; norm_num)
      have := hpair σ b _ _ p hpa ⟨hpB1, hs⟩
      simp only [M2Glue2.trans] at this ⊢
      rw [hA, gglue_of_one hc1]
      refine this.trans ?_
      have : B0 ≤ cB B0 (j + 1) := by
        have := cB_mono hB0 (Nat.zero_le (j + 1)); simpa [cB] using this
      have hn : 0 ≤ rho p ^ 2 * s := by positivity
      calc B0 * rho p ^ 2 * s = B0 * (rho p ^ 2 * s) := by ring
        _ ≤ cB B0 (j + 1) * (rho p ^ 2 * s) := mul_le_mul_of_nonneg_right this hn
        _ = cB B0 (j + 1) * rho p ^ 2 * s := by ring
    · have hpj : p ∈ Useq R j := hp.2 h1
      have ihp := ih (by omega) p hpj σ b hpa
      rcases eq_or_lt_of_le (Cj_mem (j + 1) p).1 with h0 | h0
      · have hc0 : cs v R (j + 1) (iota v p) = 0 := by rw [hc, ← h0]
        simp only [M2Glue2.trans] at ihp ⊢
        rw [hA, gglue_of_zero hc0]
        refine ihp.trans ?_
        rw [hcB]
        have := frobNorm_nonneg (((Aseq v R gs j (iota v p) * (gs σ b (iota v p))⁻¹ : SU2) : M2) - 1)
        nlinarith
      · have hs : hsP (ordA (j + 1)).1 (ordA (j + 1)).2 p := hs_of_capC_pos h0
        have ihq := ih (by omega) p hpj _ _ ⟨hpB1, hs⟩
        simp only [M2Glue2.trans] at ihp ihq ⊢
        have hcm : 0 ≤ cs v R (j + 1) (iota v p) ∧ cs v R (j + 1) (iota v p) ≤ 1 := by
          rw [hc]; exact Cj_mem _ _
        have hne : cs v R (j + 1) (iota v p) ≠ 1 := by rw [hc]; exact ne_of_lt h1
        rw [hA, gglue, kglue, if_neg hne]
        simp only [M2Glue2.trans]
        have := close_step hcm ihp ihq hsm'
        rw [hcB]
        calc _ ≤ (11 / 2) * (cB B0 j * rho p ^ 2 * s) := this
          _ = 11 / 2 * cB B0 j * rho p ^ 2 * s := by ring

/-- the argmax direction: a cap with value `1` at every point. -/
theorem exists_cap_one (p : Z3) : ∃ σ b, hsP σ b p ∧ capC σ b p = 1 := by
  have key : ∃ σ, ∀ i, |qc p i| ≤ |qc p σ| := by
    by_cases h01 : |qc p 1| ≤ |qc p 0|
    · by_cases h02 : |qc p 2| ≤ |qc p 0|
      · exact ⟨0, fun i => by fin_cases i <;> simp <;> linarith⟩
      · exact ⟨2, fun i => by fin_cases i <;> simp <;> linarith⟩
    · by_cases h12 : |qc p 2| ≤ |qc p 1|
      · exact ⟨1, fun i => by fin_cases i <;> simp <;> linarith⟩
      · exact ⟨2, fun i => by fin_cases i <;> simp <;> linarith⟩
  obtain ⟨σ, hσ⟩ := key
  have hs : hsP σ (decide (0 ≤ p σ)) p := by
    unfold hsP
    by_cases h : 0 ≤ p σ
    · left; exact ⟨by simp [h], h⟩
    · right; exact ⟨by simp [h], by omega⟩
  refine ⟨σ, _, hs, capC_one hs ?_⟩
  unfold Qf
  have a := hσ 0; have b := hσ 1; have c := hσ 2
  rw [← sq_abs (qc p σ)]
  have := sq_nonneg |qc p σ|
  have e : ∀ i, qc p i ^ 2 ≤ |qc p σ| ^ 2 := by
    intro i
    rw [← sq_abs (qc p i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hσ i) 2
  have e0 := e 0; have e1 := e 1; have e2 := e 2
  linarith

theorem Useq_five (R : ℕ) : Box R ⊆ Useq R 5 := by
  intro p hp
  obtain ⟨σ, b, hs, h1⟩ := exists_cap_one p
  have hj := idxA_le σ b
  have hmem : p ∈ Useq R (idxA σ b) := by
    have ho := ordA_idxA σ b
    cases hk : idxA σ b with
    | zero =>
      rw [hk] at ho
      refine ⟨hp, ?_⟩
      rw [ho]; exact hs
    | succ k =>
      refine ⟨hp, fun hlt => ?_⟩
      exfalso
      have : Cj (k + 1) p = 1 := by
        unfold Cj; rw [← hk, ho]; exact h1
      rw [this] at hlt; exact lt_irrefl _ hlt
  have mono : ∀ i j, i ≤ j → Useq R i ⊆ Useq R j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (Useq_mono R _)
  exact mono _ 5 hj hmem

end AdalyFormal.M2Glue3
