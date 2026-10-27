import GV8

/-!
# GV9 -- near field and assembly on prepared charts (m2_glue3, 2026-10-15)

* `crude_bond`, `crude_sten`: a gauge `k·g` with `|k − 1| ≤ e` on a bond / stencil is a chart there if `g` is.
* `vertex_core`: six prepared half-space charts (local flatness `A₀ ρ s`, stencils `s`, pairwise transitions
  `B₀ ρ² s`) glue to ONE coordinate chart `Aseq 5` on the whole `Box R`, bounds `KT1 · ρ · s`, `KT2 · s`,
  and `Aseq 5` stays `cB 5 · ρ² s`-close to every prepared chart on its half-space.
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
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg)

variable {L : PeriodicLatticeExtent}

theorem frob_sub_le_of {a b : SU2} {e : ℝ} (ha : frobNorm ((a : M2) - 1) ≤ e) (hb : frobNorm ((b : M2) - 1) ≤ e) :
    frobNorm ((a : M2) - (b : M2)) ≤ 2 * e := by
  have := frobNorm_sub_le' (a : M2) 1 (b : M2)
  rw [frobNorm_sub_comm (1 : M2) (b : M2)] at this
  linarith

theorem crude_bond {k0 k1 G : SU2} {e : ℝ} (h0 : frobNorm ((k0 : M2) - 1) ≤ e) (h1 : frobNorm ((k1 : M2) - 1) ≤ e) :
    frobNorm (((k0 * G * k1⁻¹ : SU2) : M2) - 1) ≤ frobNorm ((G : M2) - 1) + 2 * e := by
  refine (gauge_step_one k0 k1 G).trans ?_
  have := frob_sub_le_of h1 h0
  linarith

theorem crude_sten {k0 k1 k2 k3 G G' : SU2} {e g t : ℝ} (he : 0 ≤ e)
    (h0 : frobNorm ((k0 : M2) - 1) ≤ e) (h1 : frobNorm ((k1 : M2) - 1) ≤ e)
    (h2 : frobNorm ((k2 : M2) - 1) ≤ e) (h3 : frobNorm ((k3 : M2) - 1) ≤ e)
    (hG : frobNorm ((G : M2) - 1) ≤ g) (hGG : frobNorm ((G' : M2) - (G : M2)) ≤ t) :
    frobNorm (((k2 * G' * k3⁻¹ : SU2) : M2) - ((k0 * G * k1⁻¹ : SU2) : M2)) ≤ t + g * (4 * e) + 4 * e ^ 2 + 4 * e := by
  refine (gauge_step_two k0 k1 k2 k3 G G').trans ?_
  have a20 := frob_sub_le_of h2 h0
  have a31 := frob_sub_le_of h3 h1
  have a32 := frob_sub_le_of h3 h2
  have a4 : frobNorm ((k3 : M2) - k2 - ((k1 : M2) - k0)) ≤ 4 * e := by
    have e4 : (k3 : M2) - k2 - ((k1 : M2) - k0) = ((k3 : M2) - 1) - ((k2 : M2) - 1) - ((k1 : M2) - 1) + ((k0 : M2) - 1) := by
      abel
    rw [e4]
    have := frobNorm_add_le (((k3 : M2) - 1) - ((k2 : M2) - 1) - ((k1 : M2) - 1)) ((k0 : M2) - 1)
    have := AdalyFormal.Balaban.RegularityGap.frobNorm_sub_le (((k3 : M2) - 1) - ((k2 : M2) - 1)) ((k1 : M2) - 1)
    have := AdalyFormal.Balaban.RegularityGap.frobNorm_sub_le ((k3 : M2) - 1) ((k2 : M2) - 1)
    linarith
  have hg0 : 0 ≤ g := (frobNorm_nonneg _).trans hG
  have p1 : frobNorm ((G : M2) - 1) * (frobNorm ((k2 : M2) - k0) + frobNorm ((k3 : M2) - k1)) ≤ g * (4 * e) :=
    mul_le_mul hG (by linarith) (add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)) hg0
  have p2 : frobNorm ((k2 : M2) - k0) * frobNorm ((k3 : M2) - k2) ≤ (2 * e) * (2 * e) :=
    mul_le_mul a20 a32 (frobNorm_nonneg _) (by linarith)
  nlinarith

theorem gauge_factor (U : LinkCfg L) (g A : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) (ν : Fin 3) :
    periodicGaugeTransform A U (x, ν)
      = trans g A x * periodicGaugeTransform g U (x, ν) * (trans g A (periodicLatticeShift x ν))⁻¹ := by
  simp only [periodicGaugeTransform, M2Glue2.trans]; group

/-! ## constants of the vertex chart -/

noncomputable def eS (B0 : ℝ) : ℝ := cB B0 5 * 612 ^ 2
noncomputable def KT1 (A0 B0 : ℝ) : ℝ := cA A0 B0 5 + A0 + 2 * eS B0
noncomputable def KT2 (A0 B0 : ℝ) : ℝ := cC A0 B0 5 + 1 + 4 * A0 * 606 * eS B0 + 4 * eS B0 ^ 2 + 4 * eS B0

/-- a half-space containing a whole bond / stencil: take a direction not among its directions. -/
theorem exists_other (μ ν : Fin 3) : ∃ σ, σ ≠ μ ∧ σ ≠ ν := by
  fin_cases μ <;> fin_cases ν
  all_goals first
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩

theorem hsP_shift {σ : Fin 3} {b : Bool} {p : Z3} {μ : Fin 3} (h : σ ≠ μ) :
    hsP σ b (p + ev μ) ↔ hsP σ b p := by
  unfold hsP; simp [ev, h]

theorem hsP_sign (σ : Fin 3) (p : Z3) : hsP σ (decide (0 ≤ p σ)) p := by
  unfold hsP
  by_cases h : 0 ≤ p σ
  · left; exact ⟨by simp [h], h⟩
  · right; exact ⟨by simp [h], by omega⟩

theorem rho_le_box {R : ℕ} {p : Z3} (hp : p ∈ Box R) : rho p ≤ 3 * R + 3 / 2 := by
  unfold rho qc
  have e : ∀ i, |(p i : ℝ) + 1 / 2| ≤ R + 1 / 2 := by
    intro i
    have := hp i
    have h : |(p i : ℝ)| ≤ R := by rw [← Int.cast_abs]; exact_mod_cast this
    calc |(p i : ℝ) + 1 / 2| ≤ |(p i : ℝ)| + |(1 / 2 : ℝ)| := abs_add_le _ _
      _ ≤ R + 1 / 2 := by rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]; linarith
  linarith [e 0, e 1, e 2]

/-- **the vertex chart from six prepared half-space charts.** -/
theorem vertex_core {U : LinkCfg L} {v : PeriodicLatticeSite L} {R : ℕ} (hinj : Set.InjOn (iota v) (Box (R + 2)))
    {gs : Fin 3 → Bool → PeriodicLatticeSite L → SU2} {A0 B0 s : ℝ} (hA0 : 0 ≤ A0) (hB0 : 0 ≤ B0) (hs0 : 0 ≤ s)
    (hZ : ∀ σ b, ZCh U (gs σ b) v (Hd R σ b) (fun p => A0 * rho p * s) (fun _ => s))
    (hpair : ∀ σ b σ' b' p, p ∈ Hd R σ b → p ∈ Hd R σ' b' →
      frobNorm (((trans (gs σ b) (gs σ' b') (iota v p) : SU2) : M2) - 1) ≤ B0 * rho p ^ 2 * s)
    (hsmall : ∀ p ∈ Box R, (4 * cB B0 5 + 1) * rho p ^ 2 * s ≤ 1) :
    ZCh U (Aseq v R gs 5) v (Box R) (fun p => KT1 A0 B0 * rho p * s) (fun _ => KT2 A0 B0 * s) ∧
    ∀ p ∈ Box R, ∀ σ b, p ∈ Hd R σ b →
      frobNorm (((trans (gs σ b) (Aseq v R gs 5) (iota v p) : SU2) : M2) - 1) ≤ cB B0 5 * rho p ^ 2 * s := by
  have hinj1 : Set.InjOn (iota v) (Box (R + 1)) := hinj.mono (Box_mono (Nat.le_succ _))
  have hcB := cB_nonneg hB0 5
  have hsm2 : ∀ p ∈ Box R, cB B0 5 * rho p ^ 2 * s ≤ 2 := by
    intro p hp; have := hsmall p hp
    have : 0 ≤ rho p ^ 2 * s := by positivity
    nlinarith
  have hcl := close_seq (U := U) hinj1 hB0 hs0 hpair hsm2 5 le_rfl
  have hclose : ∀ p ∈ Box R, ∀ σ b, p ∈ Hd R σ b →
      frobNorm (((trans (gs σ b) (Aseq v R gs 5) (iota v p) : SU2) : M2) - 1) ≤ cB B0 5 * rho p ^ 2 * s :=
    fun p hp => hcl p (Useq_five R hp)
  have hfar := zch_seq (U := U) hinj hA0 hB0 hs0 hZ hpair hsmall 5 le_rfl
  have hcA := cA_ge hA0 hB0 5
  have hcC := cC_ge hA0 hB0 5
  have heS : 0 ≤ eS B0 := by unfold eS; positivity
  -- `s ≤ 1`
  have hs1 : s ≤ 1 := by
    by_cases hR : (Box R).Nonempty
    · obtain ⟨p, hp⟩ := hR
      have h1 := hsmall p hp; have := rho_ge p
      have h2 : (9 / 4 : ℝ) ≤ rho p ^ 2 := by nlinarith
      have e1 : rho p ^ 2 * s ≤ (4 * cB B0 5 + 1) * rho p ^ 2 * s := by
        have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hcB) (mul_nonneg (sq_nonneg (rho p)) hs0)
        nlinarith
      have e2 : (9 / 4) * s ≤ rho p ^ 2 * s := mul_le_mul_of_nonneg_right h2 hs0
      linarith
    · -- empty box cannot happen (`0 ∈ Box R`)
      exact absurd ⟨0, fun i => by simp⟩ hR
  -- closeness near the vertex, in the form `e`
  have near_e : ∀ p, p ∈ Box R → rho p < 612 → ∀ σ b, p ∈ Hd R σ b →
      frobNorm (((trans (gs σ b) (Aseq v R gs 5) (iota v p) : SU2) : M2) - 1) ≤ eS B0 * s := by
    intro p hp hρ σ b hpa
    refine (hclose p hp σ b hpa).trans ?_
    unfold eS
    have : rho p ^ 2 ≤ 612 ^ 2 := by have := rho_pos p; nlinarith
    have : cB B0 5 * rho p ^ 2 ≤ cB B0 5 * 612 ^ 2 := mul_le_mul_of_nonneg_left this hcB
    nlinarith
  refine ⟨⟨fun p ν hp hpν => ?_, fun p μ ν h0 h1 h2 h3 => ?_⟩, hclose⟩
  · -- bonds
    have hρ0 := rho_pos p
    by_cases hF : p ∈ Fseq R 5 ∧ p + ev ν ∈ Fseq R 5
    · refine (hfar.1 p ν hF.1 hF.2).trans ?_
      show cA A0 B0 5 * rho p * s ≤ KT1 A0 B0 * rho p * s
      unfold KT1
      have : 0 ≤ rho p * s := by positivity
      nlinarith
    · -- near the vertex
      have hnear : rho p < 603 := by
        by_contra hc; push Not at hc
        have d1 := (rho_perturb (fun i => abs_qc_add_ev_le p ν i)).2
        exact hF ⟨Fseq_cover hp (by linarith), Fseq_cover hpν (by linarith)⟩
      have hnear1 : rho (p + ev ν) < 612 := by
        have := (rho_perturb (fun i => abs_qc_add_ev_le p ν i)).1; linarith
      obtain ⟨σ, hσν, -⟩ := exists_other ν ν
      set b := decide (0 ≤ p σ)
      have ha0 : p ∈ Hd R σ b := ⟨Box_mono (Nat.le_succ R) hp, hsP_sign σ p⟩
      have ha1 : p + ev ν ∈ Hd R σ b := ⟨Box_mono (Nat.le_succ R) hpν, (hsP_shift hσν).2 (hsP_sign σ p)⟩
      rw [gauge_factor U (gs σ b) (Aseq v R gs 5) (iota v p) ν, iota_shift]
      refine (crude_bond (near_e p hp (by linarith) σ b ha0) (near_e _ hpν hnear1 σ b ha1)).trans ?_
      have hG := (hZ σ b).1 p ν ha0 ha1
      show frobNorm (((periodicGaugeTransform (gs σ b) U (iota v p, ν) : SU2) : M2) - 1) + 2 * (eS B0 * s)
        ≤ KT1 A0 B0 * rho p * s
      unfold KT1
      have h1 : 1 ≤ rho p := by linarith [rho_ge p]
      have : 2 * (eS B0 * s) ≤ 2 * eS B0 * rho p * s := by
        have : 0 ≤ eS B0 * s := by positivity
        nlinarith
      have : 0 ≤ cA A0 B0 5 * rho p * s := by have := hA0.trans hcA; positivity
      nlinarith
  · -- stencils
    have hρ0 := rho_pos p
    by_cases hF : p ∈ Fseq R 5 ∧ p + ev ν ∈ Fseq R 5 ∧ p + ev μ ∈ Fseq R 5 ∧ p + ev μ + ev ν ∈ Fseq R 5
    · refine (hfar.2 p μ ν hF.1 hF.2.1 hF.2.2.1 hF.2.2.2).trans ?_
      show cC A0 B0 5 * s ≤ KT2 A0 B0 * s
      unfold KT2
      have : 0 ≤ 4 * A0 * 606 * eS B0 := by positivity
      nlinarith
    · have dd := qc_diff_le p μ ν
      have r1 := (rho_perturb (fun i => (dd i).1))
      have r2 := (rho_perturb (fun i => (dd i).2.1))
      have r3 := (rho_perturb (fun i => (dd i).2.2))
      have hnear : rho p < 606 := by
        by_contra hc; push Not at hc
        exact hF ⟨Fseq_cover h0 (by linarith), Fseq_cover h1 (by linarith [r1.2]),
          Fseq_cover h2 (by linarith [r2.2]), Fseq_cover h3 (by linarith [r3.2])⟩
      obtain ⟨σ, hσμ, hσν⟩ := exists_other μ ν
      set b := decide (0 ≤ p σ)
      have hs0' := hsP_sign σ p
      have ha0 : p ∈ Hd R σ b := ⟨Box_mono (Nat.le_succ R) h0, hs0'⟩
      have ha1 : p + ev ν ∈ Hd R σ b := ⟨Box_mono (Nat.le_succ R) h1, (hsP_shift hσν).2 hs0'⟩
      have ha2 : p + ev μ ∈ Hd R σ b := ⟨Box_mono (Nat.le_succ R) h2, (hsP_shift hσμ).2 hs0'⟩
      have ha3 : p + ev μ + ev ν ∈ Hd R σ b :=
        ⟨Box_mono (Nat.le_succ R) h3, (hsP_shift hσν).2 ((hsP_shift hσμ).2 hs0')⟩
      rw [gauge_factor U (gs σ b) (Aseq v R gs 5) (iota v (p + ev μ)) ν,
        gauge_factor U (gs σ b) (Aseq v R gs 5) (iota v p) ν, iota_shift, iota_shift]
      have k0 := near_e p h0 (by linarith) σ b ha0
      have k1 := near_e _ h1 (by linarith [r1.1]) σ b ha1
      have k2 := near_e _ h2 (by linarith [r2.1]) σ b ha2
      have k3 := near_e _ h3 (by linarith [r3.1]) σ b ha3
      have hG := (hZ σ b).1 p ν ha0 ha1
      have hGG := (hZ σ b).2 p μ ν ha0 ha1 ha2 ha3
      have hc := crude_sten (by positivity) k0 k1 k2 k3 hG hGG
      refine hc.trans ?_
      show s + A0 * rho p * s * (4 * (eS B0 * s)) + 4 * (eS B0 * s) ^ 2 + 4 * (eS B0 * s) ≤ KT2 A0 B0 * s
      unfold KT2
      have q1 : A0 * rho p * s * (4 * (eS B0 * s)) ≤ 4 * A0 * 606 * eS B0 * s := by
        have : rho p * s ≤ 606 := by nlinarith
        have : 0 ≤ A0 * (4 * eS B0 * s) := by positivity
        nlinarith
      have q2 : 4 * (eS B0 * s) ^ 2 ≤ 4 * eS B0 ^ 2 * s := by
        have : s ^ 2 ≤ s := by nlinarith
        have : 0 ≤ eS B0 ^ 2 := by positivity
        nlinarith
      have : 0 ≤ cC A0 B0 5 * s := by positivity
      nlinarith

end AdalyFormal.M2Glue3
