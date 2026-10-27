import UW10
import UZ5

/-!
# UW11 -- **`BallChartsGU` for `j ≥ 2` from the cell charts of the interface** (lane unif_20261016)

* `Box3`, `cb base s lo hi` : the box of cells with relative indices in `[lo μ, hi μ]` (cell side `s`, origin `base`).
* `stack_cb` : `stack_dir` in cell-box coordinates.
* `cellBox_eq`, `cb_sub_BoxR`, `BoxR_sub_cb` : the cell boxes of the interface are cell boxes `cb`, and the box `BoxR` is the
  full box of `2n + 1` cells per direction.
* `box_chart` : cell charts at `(c X1, c X2)` on every full cell and the plaquette bound `c X2` on `BoxR` give ONE gauge on
  `BoxR` with constants `Kst^{6n} c X1`, `Kst^{6n} c X2`, provided `Kst^{6n} c · 12 M α₀ ≤ 1`.
* `ballChartsGUJ_ge2 : CoverGeomBoxU → BallChartsGUJ (2 ≤ ·)`.  ONLY the cell part (`c' = c`) of `CoverGeomBox` is used.
* `ballChartsGU_of_cover : CoverGeomU → CoverGeomBoxU → BallChartsGU`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist bigSide)
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (GChart GChart.mono)
open AdalyFormal.M2BallCharts (Bz)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.UnifLane (ClassFamU BallChartsGU)

/-- a coordinate box. -/
def Box3 (lo hi : Z3) : Set Z3 := {p | ∀ μ, lo μ ≤ p μ ∧ p μ ≤ hi μ}

/-- the box of cells with relative indices `lo μ ≤ i ≤ hi μ`. -/
def cb (base : Z3) (s : ℤ) (lo hi : Fin 3 → ℕ) : Set Z3 :=
  Box3 (fun μ => base μ + (lo μ : ℤ) * s) (fun μ => base μ + ((hi μ : ℤ) + 1) * s - 1)

theorem cb_slab (base : Z3) (s : ℤ) (lo hi : Fin 3 → ℕ) (σ : Fin 3) (a b : ℕ) :
    cb base s (Function.update lo σ a) (Function.update hi σ b)
      = SlabS σ (fun μ => base μ + (lo μ : ℤ) * s) (fun μ => base μ + ((hi μ : ℤ) + 1) * s - 1)
          (base σ + (a : ℤ) * s) (base σ + ((b : ℤ) + 1) * s) := by
  ext p
  simp only [cb, Box3, SlabS, TrB, Set.mem_setOf_eq, Function.update_apply]
  constructor
  · intro h
    refine ⟨fun ν hν => ?_, ?_, ?_⟩
    · have := h ν; rw [if_neg hν, if_neg hν] at this; exact this
    · have := (h σ).1; rw [if_pos rfl] at this; exact this
    · have := (h σ).2; rw [if_pos rfl] at this; linarith
  · rintro ⟨ht, h1, h2⟩ μ
    by_cases hμ : μ = σ
    · rw [if_pos hμ, if_pos hμ, hμ]; constructor <;> linarith
    · rw [if_neg hμ, if_neg hμ]; exact ht μ hμ

/-- **stacking along `σ` in cell-box coordinates.** -/
theorem stack_cb (W : Z3 → Fin 3 → SU2) {σ τ₁ τ₂ : Fin 3} (hτ : ∀ ν, ν ≠ σ → ν = τ₁ ∨ ν = τ₂) (h1σ : τ₁ ≠ σ)
    (h2σ : τ₂ ≠ σ) (base : Z3) {s : ℤ} (hs : 2 ≤ s) (lo hi : Fin 3 → ℕ) (hlh : ∀ ν, lo ν ≤ hi ν) (hlo : lo σ = 0)
    (N : ℕ) (hhi : hi σ = N) {w : ℕ} (hw : 1 ≤ w) {Y A : ℝ} (hY : 0 ≤ Y) (hA : 0 ≤ A)
    (hsm : Kst ^ N * A * w * w * Y ≤ 1)
    (hp : ∀ i : ℕ, i ≤ N → Ch W (cb base s (Function.update lo σ i) (Function.update hi σ i)) A w Y)
    (hH : HolB W (cb base s lo hi) (A * Y)) : Ch W (cb base s lo hi) (Kst ^ N * A) w Y := by
  have eall : cb base s lo hi = cb base s (Function.update lo σ 0) (Function.update hi σ N) := by
    have e1 : Function.update lo σ 0 = lo := by rw [← hlo]; exact Function.update_eq_self σ lo
    have e2 : Function.update hi σ N = hi := by rw [← hhi]; exact Function.update_eq_self σ hi
    rw [e1, e2]
  rw [eall, cb_slab] at hH ⊢
  simp only [Nat.cast_zero, zero_mul, add_zero] at hH ⊢
  have hlhS : ∀ ν, ν ≠ σ → base ν + (lo ν : ℤ) * s ≤ base ν + ((hi ν : ℤ) + 1) * s - 1 := by
    intro ν _
    have h' : (lo ν : ℤ) ≤ hi ν := by exact_mod_cast hlh ν
    nlinarith
  refine stack_dir W hτ h1σ h2σ hlhS hs hw hY hA N hsm (fun i hi => ?_) hH
  have := hp i hi
  rwa [cb_slab] at this

theorem cellBox_eq {s : ℤ} (hs : 0 < s) (o I : Z3) (idx : Fin 3 → ℕ) :
    cellBox s o (fun μ => I μ + (idx μ : ℤ)) = cb (fun μ => I μ * s - o μ) s idx idx := by
  ext p
  simp only [cellBox, cb, Box3, Set.mem_setOf_eq, cellZ]
  refine forall_congr' (fun μ => ?_)
  rw [div_eq_iff' hs]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

theorem cb_sub_BoxR {s : ℤ} (hs : 0 < s) (o : Z3) (n : ℕ) (lo hi : Fin 3 → ℕ) (hhi : ∀ μ, hi μ ≤ 2 * n) :
    cb (fun μ => (o μ / s - n) * s - o μ) s lo hi ⊆ BoxR s o n := by
  intro p hp μ
  obtain ⟨h1, h2⟩ := hp μ
  have hk := (div_eq_iff' hs).mp (rfl : (p μ + o μ) / s = (p μ + o μ) / s)
  set k := (p μ + o μ) / s with hkd
  show o μ / s - n ≤ k ∧ k ≤ o μ / s + n
  set I := o μ / s - (n : ℤ) with hI
  have hlo0 : (0 : ℤ) ≤ (lo μ : ℤ) * s := by positivity
  have hhi' : ((hi μ : ℤ) + 1) * s ≤ (2 * (n : ℤ) + 1) * s := by
    have : (hi μ : ℤ) ≤ 2 * n := by exact_mod_cast hhi μ
    exact mul_le_mul_of_nonneg_right (by linarith) hs.le
  constructor
  · by_contra hc
    have h' : 0 ≤ I - (k + 1) := by linarith
    have := mul_nonneg h' hs.le
    nlinarith
  · by_contra hc
    have h' : 0 ≤ k - (I + 2 * n + 1) := by linarith
    have := mul_nonneg h' hs.le
    nlinarith

theorem BoxR_sub_cb {s : ℤ} (hs : 0 < s) (o : Z3) (n : ℕ) (lo hi : Fin 3 → ℕ) (hlo : ∀ μ, lo μ = 0)
    (hhi : ∀ μ, hi μ = 2 * n) : BoxR s o n ⊆ cb (fun μ => (o μ / s - n) * s - o μ) s lo hi := by
  intro p hp μ
  obtain ⟨h1, h2⟩ := hp μ
  have hk := (div_eq_iff' hs).mp (rfl : (p μ + o μ) / s = (p μ + o μ) / s)
  simp only [cellZ] at h1 h2
  set k := (p μ + o μ) / s with hkd
  dsimp only
  rw [hlo μ, hhi μ]
  push_cast
  have a1 := mul_nonneg (show (0 : ℤ) ≤ k - (o μ / s - n) by linarith) hs.le
  have a2 := mul_nonneg (show (0 : ℤ) ≤ (o μ / s + n) - k by linarith) hs.le
  constructor <;> nlinarith

theorem upd0 (a b c x : ℕ) : Function.update ![a, b, c] 0 x = ![x, b, c] := by
  funext μ; fin_cases μ <;> simp
theorem upd1 (a b c x : ℕ) : Function.update ![a, b, c] 1 x = ![a, x, c] := by
  funext μ; fin_cases μ <;> simp
theorem upd2 (a b c x : ℕ) : Function.update ![a, b, c] 2 x = ![a, b, x] := by
  funext μ; fin_cases μ <;> simp

theorem le3 {a b c n : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) : ∀ μ, (![a, b, c] : Fin 3 → ℕ) μ ≤ n := by
  intro μ; fin_cases μ <;> simpa

theorem lehi {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    ∀ μ, (![a, b, c] : Fin 3 → ℕ) μ ≤ (![a', b', c'] : Fin 3 → ℕ) μ := by
  intro μ; fin_cases μ <;> simpa

/-- **the box chart.** -/
theorem box_chart (W : Z3 → Fin 3 → SU2) {s : ℤ} (hs : 2 ≤ s) (o : Z3) (n : ℕ) {w : ℕ} (hw : 1 ≤ w) {Y c : ℝ}
    (hY : 0 ≤ Y) (hc : 0 ≤ c)
    (hsm : Kst ^ (2 * n) * (Kst ^ (2 * n) * (Kst ^ (2 * n) * c)) * w * w * Y ≤ 1)
    (hcell : ∀ cc : Z3, (∀ μ, o μ / s - n ≤ cc μ ∧ cc μ ≤ o μ / s + n) →
      ∃ G : Z3 → SU2, C1 W G (cellBox s o cc) (c * (w * Y)) ∧ C2 W G (cellBox s o cc) (c * Y))
    (hH : HolB W (BoxR s o n) (c * Y)) :
    Ch W (BoxR s o n) (Kst ^ (2 * n) * (Kst ^ (2 * n) * (Kst ^ (2 * n) * c))) w Y := by
  have hs0 : (0 : ℤ) < s := by omega
  have hK := one_le_Kst
  have hK0 : (0 : ℝ) ≤ Kst := by linarith
  set I : Z3 := fun μ => o μ / s - n with hId
  set base : Z3 := fun μ => (o μ / s - n) * s - o μ with hbase
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hY' : 0 ≤ (w : ℝ) * w * Y := by positivity
  set A1 := Kst ^ (2 * n) * c
  set A2 := Kst ^ (2 * n) * A1
  set A3 := Kst ^ (2 * n) * A2
  have hKp : (1 : ℝ) ≤ Kst ^ (2 * n) := one_le_pow₀ hK
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  have hcA1 : c ≤ A1 := by nlinarith
  have hA12 : A1 ≤ A2 := by nlinarith
  have hA23 : A2 ≤ A3 := by nlinarith
  have hsm3 : A3 * w * w * Y ≤ 1 := hsm
  have hsm2 : A2 * w * w * Y ≤ 1 := by
    have : A2 * w * w * Y ≤ A3 * w * w * Y := by
      have e1 : A2 * w * w * Y = A2 * (w * w * Y) := by ring
      have e2 : A3 * w * w * Y = A3 * (w * w * Y) := by ring
      rw [e1, e2]; exact mul_le_mul_of_nonneg_right hA23 hY'
    linarith
  have hsm1 : A1 * w * w * Y ≤ 1 := by
    have : A1 * w * w * Y ≤ A2 * w * w * Y := by
      have e1 : A1 * w * w * Y = A1 * (w * w * Y) := by ring
      have e2 : A2 * w * w * Y = A2 * (w * w * Y) := by ring
      rw [e1, e2]; exact mul_le_mul_of_nonneg_right hA12 hY'
    linarith
  have hsub : ∀ lo hi : Fin 3 → ℕ, (∀ μ, hi μ ≤ 2 * n) → cb base s lo hi ⊆ BoxR s o n :=
    fun lo hi h => cb_sub_BoxR hs0 o n lo hi h
  have hHc : ∀ (lo hi : Fin 3 → ℕ) (B : ℝ), c ≤ B → (∀ μ, hi μ ≤ 2 * n) → HolB W (cb base s lo hi) (B * Y) :=
    fun lo hi B hB h => holB_mono hH (hsub lo hi h) (mul_le_mul_of_nonneg_right hB hY)
  have t0 : (∀ ν : Fin 3, ν ≠ 0 → ν = 1 ∨ ν = 2) := by decide
  have t1 : (∀ ν : Fin 3, ν ≠ 1 → ν = 0 ∨ ν = 2) := by decide
  have t2 : (∀ ν : Fin 3, ν ≠ 2 → ν = 0 ∨ ν = 1) := by decide
  -- cells
  have cell : ∀ i0 i1 i2 : ℕ, i0 ≤ 2 * n → i1 ≤ 2 * n → i2 ≤ 2 * n →
      Ch W (cb base s ![i0, i1, i2] ![i0, i1, i2]) c w Y := by
    intro i0 i1 i2 h0 h1 h2
    have hr : ∀ μ, o μ / s - n ≤ (fun μ => I μ + ((![i0, i1, i2] : Fin 3 → ℕ) μ : ℤ)) μ ∧
        (fun μ => I μ + ((![i0, i1, i2] : Fin 3 → ℕ) μ : ℤ)) μ ≤ o μ / s + n := by
      intro μ
      have := le3 h0 h1 h2 μ
      have : (((![i0, i1, i2] : Fin 3 → ℕ) μ : ℕ) : ℤ) ≤ 2 * n := by exact_mod_cast this
      simp only [hId]; constructor <;> push_cast <;> omega
    obtain ⟨G, g1, g2⟩ := hcell _ hr
    rw [cellBox_eq hs0 o I] at g1 g2
    refine ⟨G, g1.mono ?_ (le_of_eq (by ring)), g2.mono ?_ le_rfl⟩ <;>
    · intro p hp; simpa [hbase, hId] using hp
  -- rows (σ = 0)
  have row : ∀ i1 i2 : ℕ, i1 ≤ 2 * n → i2 ≤ 2 * n → Ch W (cb base s ![0, i1, i2] ![2 * n, i1, i2]) A1 w Y := by
    intro i1 i2 h1 h2
    refine stack_cb W t0 (by decide) (by decide) base hs ![0, i1, i2] ![2 * n, i1, i2]
      (lehi (Nat.zero_le _) le_rfl le_rfl) rfl (2 * n) rfl hw hY hc hsm1 (fun i hi => ?_)
      (hHc _ _ c le_rfl (le3 le_rfl h1 h2))
    rw [upd0, upd0]; exact cell i i1 i2 hi h1 h2
  -- layers (σ = 1)
  have layer : ∀ i2 : ℕ, i2 ≤ 2 * n → Ch W (cb base s ![0, 0, i2] ![2 * n, 2 * n, i2]) A2 w Y := by
    intro i2 h2
    refine stack_cb W t1 (by decide) (by decide) base hs ![0, 0, i2] ![2 * n, 2 * n, i2]
      (lehi (Nat.zero_le _) (Nat.zero_le _) le_rfl) rfl (2 * n) rfl hw hY hA1 hsm2 (fun i hi => ?_)
      (hHc _ _ A1 hcA1 (le3 le_rfl le_rfl h2))
    rw [upd1, upd1]; exact row i i2 hi h2
  -- box (σ = 2)
  have box : Ch W (cb base s ![0, 0, 0] ![2 * n, 2 * n, 2 * n]) A3 w Y := by
    refine stack_cb W t2 (by decide) (by decide) base hs ![0, 0, 0] ![2 * n, 2 * n, 2 * n]
      (lehi (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)) rfl (2 * n) rfl hw hY hA2 hsm3 (fun i hi => ?_)
      (hHc _ _ A2 (hcA1.trans hA12) (le3 le_rfl le_rfl le_rfl))
    rw [upd2, upd2]; exact layer i hi
  exact box.mono (BoxR_sub_cb hs0 o n _ _ (by intro μ; fin_cases μ <;> rfl) (by intro μ; fin_cases μ <;> rfl)) le_rfl hY

end AdalyFormal.UnifLane.Z
