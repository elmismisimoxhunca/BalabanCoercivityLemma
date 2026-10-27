import BLC3

/-!
# BLC4 -- the grid in ball coordinates and the generic sweep level on cut boxes (m2_ballcharts, 2026-10-15)

Ball coordinates around `w`; vertices of the `s`-grid at `qv n = cst + s n` (`cst σ ≡ -w_σ mod s`, `cst σ ∈ (s-4-r-s, s-4-r]`).
`Ib q T`: `Box r` cut to `|p_i - q_i| ≤ s - 4` for `i ∈ T`.  Collars `acol σ k = cst σ + s k - s + 6`, width `s - 12`.
`level_Ib`: charts on `Ib (qv (n[σ ↦ k])) (insert σ T)` for every `k` (constants `t₁, t₂`) give ONE chart on `Ib (qv n) T` at
`(glueT1 t₁ τ κ₁, glueT2 t₁ t₂ τ κ₁ κ₂)`, `τ = (s - 8 + 4r) · 2t₁`, `κ = κ(s - 12)`.  Same constants for every `n`, `T`, `σ`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

def IbLo (r s : ℕ) (q : Z3) (T : Finset (Fin 3)) : Z3 :=
  fun i => if i ∈ T then max (-(r : ℤ)) (q i - ((s : ℤ) - 4)) else -(r : ℤ)
def IbHi (r s : ℕ) (q : Z3) (T : Finset (Fin 3)) : Z3 :=
  fun i => if i ∈ T then min (r : ℤ) (q i + ((s : ℤ) - 4)) else (r : ℤ)
def Ib (r s : ℕ) (q : Z3) (T : Finset (Fin 3)) : Set Z3 := IBox (IbLo r s q T) (IbHi r s q T)

theorem mem_Ib {r s : ℕ} {q : Z3} {T : Finset (Fin 3)} {p : Z3} :
    p ∈ Ib r s q T ↔ p ∈ Box r ∧ ∀ i ∈ T, |p i - q i| ≤ (s : ℤ) - 4 := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · have := h i
      simp only [IbLo, IbHi] at this
      rw [abs_le]
      split_ifs at this <;> omega
    · have := h i
      simp only [IbLo, IbHi, if_pos hi] at this
      rw [abs_le]; omega
  · rintro ⟨hb, ht⟩ i
    have := hb i
    rw [abs_le] at this
    simp only [IbLo, IbHi]
    by_cases hi : i ∈ T
    · have h2 := ht i hi
      rw [abs_le] at h2
      rw [if_pos hi, if_pos hi]; omega
    · rw [if_neg hi, if_neg hi]; omega

theorem Ib_sub_box {r s : ℕ} {q : Z3} {T : Finset (Fin 3)} : Ib r s q T ⊆ Box r := fun _ h => (mem_Ib.mp h).1

/-- grid offset in ball coordinates. -/
def cst (r s : ℕ) (w : PeriodicLatticeSite L) (σ : Fin 3) : ℤ :=
  ((s : ℤ) - 4 - r) - ((((s : ℤ) - 4 - r) + ((w σ).val : ℤ)) % (s : ℤ))

def qv (r s : ℕ) (w : PeriodicLatticeSite L) (n : Fin 3 → ℕ) : Z3 := fun i => cst r s w i + (s : ℤ) * (n i : ℤ)

def acol (r s : ℕ) (w : PeriodicLatticeSite L) (σ : Fin 3) (k : ℕ) : ℤ := cst r s w σ + (s : ℤ) * (k : ℤ) - s + 6

theorem cst_bounds (r s : ℕ) (hs : 0 < s) (w : PeriodicLatticeSite L) (σ : Fin 3) :
    cst r s w σ ≤ (s : ℤ) - 4 - r ∧ (s : ℤ) - 4 - r - s < cst r s w σ := by
  have h0 := Int.emod_nonneg (((s : ℤ) - 4 - r) + ((w σ).val : ℤ)) (by omega : (s : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos (((s : ℤ) - 4 - r) + ((w σ).val : ℤ)) (by omega : (0 : ℤ) < s)
  unfold cst; constructor <;> omega

theorem cst_grid (r s : ℕ) (w : PeriodicLatticeSite L) (σ : Fin 3) :
    (((w σ).val : ℤ) + cst r s w σ) % (s : ℤ) = 0 := by
  unfold cst
  set B : ℤ := ((s : ℤ) - 4 - r) + ((w σ).val : ℤ)
  have e : ((w σ).val : ℤ) + (((s : ℤ) - 4 - r) - B % (s : ℤ)) = (s : ℤ) * (B / (s : ℤ)) := by
    have := Int.ediv_add_emod B (s : ℤ)
    simp only [B] at this ⊢; linarith
  rw [e, Int.mul_emod_right]

/-! ## the generic level -/

theorem level_Ib {r s : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) (hs : 24 ≤ s) (w : PeriodicLatticeSite L)
    {U : LinkCfg L} (σ : Fin 3) (T : Finset (Fin 3)) (hσ : σ ∉ T) (n : Fin 3 → ℕ) {t1 t2 : ℝ}
    (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (hch : ∀ k : ℕ, ∃ g : PeriodicLatticeSite L → SU2,
      ZCh U g w (Ib r s (qv r s w (Function.update n σ k)) (insert σ T)) (fun _ => t1) (fun _ => t2))
    (hτ : ((s - 8 + 4 * r : ℕ) : ℝ) * (2 * t1) ≤ 2) :
    ∃ G : PeriodicLatticeSite L → SU2, ZCh U G w (Ib r s (qv r s w n) T)
      (fun _ => glueT1 t1 (((s - 8 + 4 * r : ℕ) : ℝ) * (2 * t1)) (kap1 ((s - 12 : ℕ) : ℝ)))
      (fun _ => glueT2 t1 t2 (((s - 8 + 4 * r : ℕ) : ℝ) * (2 * t1)) (kap1 ((s - 12 : ℕ) : ℝ))
        (kap2 ((s - 12 : ℕ) : ℝ))) := by
  choose g hg using hch
  have hs0 : 0 < s := by omega
  obtain ⟨hc1, hc2⟩ := cst_bounds r s hs0 w σ
  have hwd : ((s - 12 : ℕ) : ℤ) = (s : ℤ) - 12 := by omega
  have hdm' : ((s - 8 + 4 * r : ℕ) : ℤ) = (s : ℤ) - 8 + 4 * r := by omega
  have hgap : ∀ k, acol r s w σ k + ((s - 12 : ℕ) : ℤ) + 4 ≤ acol r s w σ (k + 1) := by
    intro k
    have e : (s : ℤ) * ((k + 1 : ℕ) : ℤ) = (s : ℤ) * (k : ℤ) + s := by push_cast; ring
    unfold acol; rw [e, hwd]; omega
  have hslab : ∀ k p, p ∈ IBox (IbLo r s (qv r s w n) T) (IbHi r s (qv r s w n) T) →
      (k = 0 ∨ acol r s w σ k - 2 ≤ p σ) → p σ ≤ acol r s w σ (k + 1) + ((s - 12 : ℕ) : ℤ) + 2 →
      p ∈ Ib r s (qv r s w (Function.update n σ k)) (insert σ T) := by
    intro k p hp h1 h2
    obtain ⟨hb, ht⟩ := mem_Ib.mp hp
    refine mem_Ib.mpr ⟨hb, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · have e : (s : ℤ) * ((k + 1 : ℕ) : ℤ) = (s : ℤ) * (k : ℤ) + s := by push_cast; ring
      simp only [qv, Function.update_self]
      unfold acol at h1 h2
      rw [e, hwd] at h2
      have hbσ := hb i
      rw [abs_le] at hbσ ⊢
      rcases h1 with h0 | h1
      · subst h0
        simp only [Nat.cast_zero, mul_zero] at h2 ⊢
        constructor <;> omega
      · constructor <;> omega
    · have hne : i ≠ σ := fun e => hσ (e ▸ hi')
      have := ht i hi'
      simp only [qv, Function.update_of_ne hne] at this ⊢
      exact this
  have hdm : ∀ k p p', p ∈ IBox (IbLo r s (qv r s w n) T) (IbHi r s (qv r s w n) T) →
      p' ∈ IBox (IbLo r s (qv r s w n) T) (IbHi r s (qv r s w n) T) →
      acol r s w σ (k + 1) - 2 ≤ p σ → p σ ≤ acol r s w σ (k + 1) + ((s - 12 : ℕ) : ℤ) + 2 →
      acol r s w σ (k + 1) - 2 ≤ p' σ → p' σ ≤ acol r s w σ (k + 1) + ((s - 12 : ℕ) : ℤ) + 2 →
      l1 p p' ≤ s - 8 + 4 * r := by
    intro k p p' hp hp' a1 a2 a3 a4
    have hb := (mem_Ib.mp hp).1; have hb' := (mem_Ib.mp hp').1
    have b0 := hb 0; have b1 := hb 1; have b2 := hb 2
    have c0 := hb' 0; have c1 := hb' 1; have c2 := hb' 2
    rw [abs_le] at b0 b1 b2 c0 c1 c2
    rw [hwd] at a2 a4
    unfold l1
    fin_cases σ <;> simp at a1 a2 a3 a4 <;> omega
  -- top of the sweep
  set N : ℕ := 2 * r + 8 with hN
  obtain ⟨G, hG⟩ := level_sweep (v := w) hL (lo := IbLo r s (qv r s w n) T) (hi := IbHi r s (qv r s w n) T)
    Ib_sub_box σ (acol r s w σ) (s - 12) (by omega) hgap g
    (fun k => Ib r s (qv r s w (Function.update n σ k)) (insert σ T)) ht1 ht2 hg hslab (s - 8 + 4 * r) hdm hτ N
  refine ⟨G, zch_mono hG (fun p hp => ⟨hp, ?_⟩) le_rfl le_rfl⟩
  have hb := (mem_Ib.mp hp).1 σ
  rw [abs_le] at hb
  have hsN : (N : ℤ) ≤ (s : ℤ) * (N : ℤ) := by
    have : (1 : ℤ) ≤ s := by omega
    nlinarith
  have e : (s : ℤ) * ((N + 1 : ℕ) : ℤ) = (s : ℤ) * (N : ℤ) + s := by push_cast; ring
  have hNz : (N : ℤ) = 2 * r + 8 := by rw [hN]; push_cast; ring
  have : p σ ≤ acol r s w σ (N + 1) + ((s - 12 : ℕ) : ℤ) + 2 := by
    unfold acol; rw [e, hwd]; omega
  have hc : ((p σ : ℤ) : ℝ) ≤ ((acol r s w σ (N + 1) + ((s - 12 : ℕ) : ℤ) + 2 : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at hc ⊢
  linarith

end AdalyFormal.M2BallCharts
