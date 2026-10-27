import DLR62
import SmoothLog
import AdalyFormal.Balaban.Bch2

/-!
# DL64 -- the EVEN-PART calculus on `SU(2)` and `𝔰𝔲(2)` (Frobenius norm), scale `τ`

`EvQ P Q Z Ke Kd τ` : `‖P + Q − 2Z‖ ≤ Ke τ²`, `‖P − Z‖ ≤ Kd τ`, `‖Q − Z‖ ≤ Kd τ`
(`P`, `Q` = the object at `+t` and `−t`, `Z` = the object at `t = 0`).  Rules, constants composing explicitly:
* `EvQ.mul` (`SU(2)` factors): `(Ke,Kd)·(Ke',Kd') ↦ (Ke + Ke' + 2KdKd', Kd + Kd')`;  `EvQ.inv` (same constants);
* `EvQ.add`, `EvQ.smul`, `EvQ.sum`, `EvQ.const`, `EvQ.mono`;
* `EvQ.exp` (base `X0` with `e^{√2‖X0‖} ≤ 2`, `Kd τ ≤ 1/2`): `↦ (4Ke + 12Kd², 7Kd)`;
* `EvQ.log` (`SU(2)`, base `g0` with `2(e^{√2‖log g0‖} − 1) ≤ 1/2`, `‖g0 − 1‖ ≤ 1`, `Kd τ ≤ 1/4`): `↦ (2Ke + 60Kd², 2Kd)`
  — via `even_exp_inv` (DL62) and Bch2 `su2Log_lipschitz`; no derivative of `log` anywhere;
* `EvQ.base` : `exp(±H)` around `1`, `‖H‖ ≤ τ ≤ 1/2`: `(6, 4)`;
* `EvQ.hol` : path holonomies of length `n` of link-wise `(ke, kd)` families: `(ke n + 2kd² n², kd n)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp su2Angle su2NegOne coe_mul coe_inv coe_one
  star_mul_self mul_star_self su2Log_antiHermitian su2Log_traceless)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

/-! ## unitary invariance -/

theorem fN_unitary_mul (W M : Mt) (hW : Wᴴ * W = 1) : frobNorm (W * M) = frobNorm M := by
  rw [← fN_conjT (W * M), Matrix.conjTranspose_mul]
  have h : Wᴴ * Wᴴᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hW
  rw [fN_mul_unitary _ _ h, fN_conjT]

theorem fN_su2_mul (g : SU2) (M : Mt) : frobNorm ((g : Mt) * M) = frobNorm M :=
  fN_unitary_mul _ M (star_mul_self g)

theorem fN_mul_su2 (M : Mt) (g : SU2) : frobNorm (M * (g : Mt)) = frobNorm M :=
  fN_mul_unitary M _ (mul_star_self g)

/-! ## the predicate -/

/-- even-part data at scale `τ` -/
structure EvQ (P Q Z : Mt) (Ke Kd τ : ℝ) : Prop where
  he : frobNorm (P + Q - 2 • Z) ≤ Ke * τ ^ 2
  hp : frobNorm (P - Z) ≤ Kd * τ
  hq : frobNorm (Q - Z) ≤ Kd * τ

theorem EvQ.mono {P Q Z : Mt} {Ke Kd Ke' Kd' τ : ℝ} (h : EvQ P Q Z Ke Kd τ) (hτ : 0 ≤ τ)
    (he : Ke ≤ Ke') (hd : Kd ≤ Kd') : EvQ P Q Z Ke' Kd' τ :=
  ⟨h.he.trans (mul_le_mul_of_nonneg_right he (by positivity)),
   h.hp.trans (mul_le_mul_of_nonneg_right hd hτ), h.hq.trans (mul_le_mul_of_nonneg_right hd hτ)⟩

theorem EvQ.const (Z : Mt) (τ : ℝ) : EvQ Z Z Z 0 0 τ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [two_nsmul, sub_self, fN_zero]; simp
  · rw [sub_self, fN_zero]; simp
  · rw [sub_self, fN_zero]; simp

theorem EvQ.Kd_nonneg' {P Q Z : Mt} {Ke Kd τ : ℝ} (h : EvQ P Q Z Ke Kd τ) : 0 ≤ Kd * τ :=
  (frobNorm_nonneg _).trans h.hp

theorem EvQ.Ke_nonneg' {P Q Z : Mt} {Ke Kd τ : ℝ} (h : EvQ P Q Z Ke Kd τ) : 0 ≤ Ke * τ ^ 2 :=
  (frobNorm_nonneg _).trans h.he

/-! ## linear rules -/

theorem EvQ.add {P Q Z P' Q' Z' : Mt} {Ke Kd Ke' Kd' τ : ℝ} (h : EvQ P Q Z Ke Kd τ) (h' : EvQ P' Q' Z' Ke' Kd' τ) :
    EvQ (P + P') (Q + Q') (Z + Z') (Ke + Ke') (Kd + Kd') τ := by
  refine ⟨?_, ?_, ?_⟩
  · have e : P + P' + (Q + Q') - 2 • (Z + Z') = (P + Q - 2 • Z) + (P' + Q' - 2 • Z') := by
      rw [two_nsmul, two_nsmul, two_nsmul]; abel
    rw [e]; refine (fN_add _ _).trans ?_; have := h.he; have := h'.he; nlinarith
  · have e : P + P' - (Z + Z') = (P - Z) + (P' - Z') := by abel
    rw [e]; refine (fN_add _ _).trans ?_; have := h.hp; have := h'.hp; nlinarith
  · have e : Q + Q' - (Z + Z') = (Q - Z) + (Q' - Z') := by abel
    rw [e]; refine (fN_add _ _).trans ?_; have := h.hq; have := h'.hq; nlinarith

theorem EvQ.smul {P Q Z : Mt} {Ke Kd τ : ℝ} (h : EvQ P Q Z Ke Kd τ) (r : ℝ) :
    EvQ (r • P) (r • Q) (r • Z) (|r| * Ke) (|r| * Kd) τ := by
  refine ⟨?_, ?_, ?_⟩
  · have e : r • P + r • Q - 2 • (r • Z) = r • (P + Q - 2 • Z) := by
      rw [smul_sub, smul_add, smul_comm r (2 : ℕ) Z]
    rw [e, fN_rsmul, mul_assoc]; exact mul_le_mul_of_nonneg_left h.he (abs_nonneg _)
  · rw [← smul_sub, fN_rsmul, mul_assoc]; exact mul_le_mul_of_nonneg_left h.hp (abs_nonneg _)
  · rw [← smul_sub, fN_rsmul, mul_assoc]; exact mul_le_mul_of_nonneg_left h.hq (abs_nonneg _)

theorem EvQ.neg {P Q Z : Mt} {Ke Kd τ : ℝ} (h : EvQ P Q Z Ke Kd τ) : EvQ (-P) (-Q) (-Z) Ke Kd τ := by
  have := h.smul (-1)
  simpa using this

theorem EvQ.sum {ι : Type*} (s : Finset ι) (P Q Z : ι → Mt) (Ke Kd : ι → ℝ) (τ : ℝ)
    (h : ∀ i ∈ s, EvQ (P i) (Q i) (Z i) (Ke i) (Kd i) τ) :
    EvQ (∑ i ∈ s, P i) (∑ i ∈ s, Q i) (∑ i ∈ s, Z i) (∑ i ∈ s, Ke i) (∑ i ∈ s, Kd i) τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EvQ.const (0 : Mt) τ
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- averaging with weight `w ≥ 0`, `w·#s ≤ 1`, uniform constants -/
theorem EvQ.avg {ι : Type*} (s : Finset ι) (w : ℝ) (hw : 0 ≤ w) (hws : w * s.card ≤ 1)
    (P Q Z : ι → Mt) (Ke Kd τ : ℝ) (hKe : 0 ≤ Ke) (hKd : 0 ≤ Kd)
    (h : ∀ i ∈ s, EvQ (P i) (Q i) (Z i) Ke Kd τ) (hτ : 0 ≤ τ) :
    EvQ (∑ i ∈ s, w • P i) (∑ i ∈ s, w • Q i) (∑ i ∈ s, w • Z i) Ke Kd τ := by
  have h1 := EvQ.sum s (fun i => w • P i) (fun i => w • Q i) (fun i => w • Z i)
    (fun _ => |w| * Ke) (fun _ => |w| * Kd) τ (fun i hi => (h i hi).smul w)
  simp only [Finset.sum_const, nsmul_eq_mul, abs_of_nonneg hw] at h1
  refine h1.mono hτ ?_ ?_
  · nlinarith
  · nlinarith

/-! ## the group rules -/

theorem EvQ.mul {p q z p' q' z' : SU2} {Ke Kd Ke' Kd' τ : ℝ}
    (h : EvQ (p : Mt) (q : Mt) (z : Mt) Ke Kd τ) (h' : EvQ (p' : Mt) (q' : Mt) (z' : Mt) Ke' Kd' τ) :
    EvQ ((p * p' : SU2) : Mt) ((q * q' : SU2) : Mt) ((z * z' : SU2) : Mt) (Ke + Ke' + 2 * Kd * Kd') (Kd + Kd') τ := by
  rw [coe_mul, coe_mul, coe_mul]
  set P : Mt := (p : Mt); set Q : Mt := (q : Mt); set Z : Mt := (z : Mt)
  set P' : Mt := (p' : Mt); set Q' : Mt := (q' : Mt); set Z' : Mt := (z' : Mt)
  have hd := h.Kd_nonneg'; have hd' := h'.Kd_nonneg'
  refine ⟨?_, ?_, ?_⟩
  · have e : P * P' + Q * Q' - 2 • (Z * Z') = (P + Q - 2 • Z) * Z' + Z * (P' + Q' - 2 • Z')
        + (P - Z) * (P' - Z') + (Q - Z) * (Q' - Z') := by
      simp only [two_nsmul, add_mul, mul_add, sub_mul, mul_sub]; abel
    rw [e]
    have t1 : frobNorm ((P + Q - 2 • Z) * Z') ≤ Ke * τ ^ 2 := by rw [fN_mul_su2]; exact h.he
    have t2 : frobNorm (Z * (P' + Q' - 2 • Z')) ≤ Ke' * τ ^ 2 := by rw [fN_su2_mul]; exact h'.he
    have t3 : frobNorm ((P - Z) * (P' - Z')) ≤ (Kd * τ) * (Kd' * τ) :=
      (fN_mul _ _).trans (mul_le_mul h.hp h'.hp (frobNorm_nonneg _) hd)
    have t4 : frobNorm ((Q - Z) * (Q' - Z')) ≤ (Kd * τ) * (Kd' * τ) :=
      (fN_mul _ _).trans (mul_le_mul h.hq h'.hq (frobNorm_nonneg _) hd)
    refine (fN_add _ _).trans ?_
    refine (add_le_add (fN_add _ _) t4).trans ?_
    refine (add_le_add (add_le_add (fN_add _ _) t3) le_rfl).trans ?_
    have := add_le_add t1 t2
    nlinarith
  · have e : P * P' - Z * Z' = (P - Z) * P' + Z * (P' - Z') := by
      simp only [sub_mul, mul_sub]; abel
    rw [e]; refine (fN_add _ _).trans ?_
    rw [fN_mul_su2, fN_su2_mul]
    have := h.hp; have := h'.hp; nlinarith
  · have e : Q * Q' - Z * Z' = (Q - Z) * Q' + Z * (Q' - Z') := by
      simp only [sub_mul, mul_sub]; abel
    rw [e]; refine (fN_add _ _).trans ?_
    rw [fN_mul_su2, fN_su2_mul]
    have := h.hq; have := h'.hq; nlinarith

theorem EvQ.inv {p q z : SU2} {Ke Kd τ : ℝ} (h : EvQ (p : Mt) (q : Mt) (z : Mt) Ke Kd τ) :
    EvQ ((p⁻¹ : SU2) : Mt) ((q⁻¹ : SU2) : Mt) ((z⁻¹ : SU2) : Mt) Ke Kd τ := by
  rw [coe_inv, coe_inv, coe_inv]
  refine ⟨?_, ?_, ?_⟩
  · have e : (p : Mt)ᴴ + (q : Mt)ᴴ - 2 • (z : Mt)ᴴ = ((p : Mt) + (q : Mt) - 2 • (z : Mt))ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_nsmul]
    rw [e, fN_conjT]; exact h.he
  · rw [← Matrix.conjTranspose_sub, fN_conjT]; exact h.hp
  · rw [← Matrix.conjTranspose_sub, fN_conjT]; exact h.hq

theorem EvQ.const1 (z : SU2) (τ : ℝ) : EvQ (z : Mt) (z : Mt) (z : Mt) 0 0 τ := EvQ.const _ τ

/-! ## exp and log -/

theorem EvQ.exp {X Y X0 : Mt} {Ke Kd τ : ℝ} (hτ : 0 ≤ τ) (h : EvQ X Y X0 Ke Kd τ) (hd : Kd * τ ≤ 1 / 2)
    (hE : Real.exp (Real.sqrt 2 * frobNorm X0) ≤ 2) :
    EvQ (NormedSpace.exp X) (NormedSpace.exp Y) (NormedSpace.exp X0) (4 * Ke + 12 * Kd ^ 2) (7 * Kd) τ := by
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hE0 : 0 ≤ Real.exp (Real.sqrt 2 * frobNorm X0) := (Real.exp_pos _).le
  have hp := h.hp; have hq := h.hq
  have hpn := frobNorm_nonneg (X - X0); have hqn := frobNorm_nonneg (Y - X0)
  have hd0 := h.Kd_nonneg'
  refine ⟨?_, ?_, ?_⟩
  · have hev := even_exp X Y X0 (hp.trans hd) (hq.trans hd)
    have he := h.he
    have he0 := h.Ke_nonneg'
    have a1 : 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (X + Y - 2 • X0) ≤ 4 * (Ke * τ ^ 2) := by
      have := mul_le_mul hE he (frobNorm_nonneg _) (by norm_num)
      nlinarith
    have hp2 : frobNorm (X - X0) ^ 2 ≤ (Kd * τ) ^ 2 := pow_le_pow_left₀ hpn hp 2
    have hq2 : frobNorm (Y - X0) ^ 2 ≤ (Kd * τ) ^ 2 := pow_le_pow_left₀ hqn hq 2
    have a2 : 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * (frobNorm (X - X0) ^ 2 + frobNorm (Y - X0) ^ 2)
        ≤ 12 * (Kd * τ) ^ 2 := by
      have hs : frobNorm (X - X0) ^ 2 + frobNorm (Y - X0) ^ 2 ≤ 2 * (Kd * τ) ^ 2 := by linarith
      have hsn : 0 ≤ frobNorm (X - X0) ^ 2 + frobNorm (Y - X0) ^ 2 := by positivity
      have b1 : 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) ≤ 2 * (3 / 2) * 2 := by
        have := mul_le_mul hs2 hE hE0 (by norm_num); nlinarith
      have b2 := mul_le_mul b1 hs hsn (by norm_num)
      nlinarith
    have : (4 * Ke + 12 * Kd ^ 2) * τ ^ 2 = 4 * (Ke * τ ^ 2) + 12 * (Kd * τ) ^ 2 := by ring
    rw [this]; linarith
  · have hl := lip_exp X X0 (hp.trans hd)
    have hp2 : frobNorm (X - X0) ^ 2 ≤ (Kd * τ) * (1 / 2) := by
      have := mul_le_mul hp (hp.trans hd) hpn hd0; nlinarith
    have b1 : 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (X - X0) ≤ 4 * (Kd * τ) := by
      have := mul_le_mul hE hp hpn (by norm_num); nlinarith
    have b2 : 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (X - X0) ^ 2 ≤ 3 * (Kd * τ) := by
      have c1 : 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) ≤ 6 := by
        have := mul_le_mul hs2 hE hE0 (by norm_num); nlinarith
      have := mul_le_mul c1 hp2 (sq_nonneg _) (by norm_num)
      nlinarith
    have : 7 * Kd * τ = 7 * (Kd * τ) := by ring
    rw [this]; linarith
  · have hl := lip_exp Y X0 (hq.trans hd)
    have hq2 : frobNorm (Y - X0) ^ 2 ≤ (Kd * τ) * (1 / 2) := by
      have := mul_le_mul hq (hq.trans hd) hqn hd0; nlinarith
    have b1 : 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (Y - X0) ≤ 4 * (Kd * τ) := by
      have := mul_le_mul hE hq hqn (by norm_num); nlinarith
    have b2 : 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) * frobNorm (Y - X0) ^ 2 ≤ 3 * (Kd * τ) := by
      have c1 : 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm X0) ≤ 6 := by
        have := mul_le_mul hs2 hE hE0 (by norm_num); nlinarith
      have := mul_le_mul c1 hq2 (sq_nonneg _) (by norm_num)
      nlinarith
    have : 7 * Kd * τ = 7 * (Kd * τ) := by ring
    rw [this]; linarith

/-- `exp (su2Log g) = g` (`g ≠ −1`), coerced -/
theorem exp_su2Log_coe (g : SU2) (hne : g ≠ su2NegOne) : NormedSpace.exp (su2Log g) = (g : Mt) :=
  AdalyFormal.Balaban.SmoothLog.exp_su2Log g hne

theorem EvQ.log {g g' g0 : SU2} {Ke Kd τ : ℝ} (hτ : 0 ≤ τ) (h : EvQ (g : Mt) (g' : Mt) (g0 : Mt) Ke Kd τ)
    (hd : Kd * τ ≤ 1 / 4) (hg0 : frobNorm ((g0 : Mt) - 1) ≤ 1)
    (hE : 2 * (Real.exp (Real.sqrt 2 * frobNorm (su2Log g0)) - 1) ≤ 1 / 2) :
    EvQ (su2Log g) (su2Log g') (su2Log g0) (2 * Ke + 60 * Kd ^ 2) (2 * Kd) τ := by
  have hpi := Real.pi_gt_three
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hd0 := h.Kd_nonneg'
  -- angles
  have hang : ∀ k : SU2, frobNorm ((k : Mt) - (g0 : Mt)) ≤ Kd * τ → su2Angle k ≤ Real.pi / 2 := by
    intro k hk
    apply AdalyFormal.Balaban.Bch2.angle_le_of_frobNorm_sub_one
    have e : (k : Mt) - 1 = ((k : Mt) - (g0 : Mt)) + ((g0 : Mt) - 1) := by abel
    rw [e]; refine (fN_add _ _).trans ?_; linarith
  have ha := hang g h.hp
  have ha' := hang g' h.hq
  have ha0 : su2Angle g0 ≤ Real.pi / 2 := hang g0 (by rw [sub_self, fN_zero]; exact hd0)
  have hne := AdalyFormal.Balaban.Bch2.ne_negOne_of_angle_le ha
  have hne' := AdalyFormal.Balaban.Bch2.ne_negOne_of_angle_le ha'
  have hne0 := AdalyFormal.Balaban.Bch2.ne_negOne_of_angle_le ha0
  -- Lipschitz
  have hl := AdalyFormal.Balaban.Bch2.su2Log_lipschitz ha ha0
  have hl' := AdalyFormal.Balaban.Bch2.su2Log_lipschitz ha' ha0
  have hX : frobNorm (su2Log g - su2Log g0) ≤ 2 * Kd * τ := by
    refine hl.trans ?_
    have := mul_le_mul (by linarith : Real.pi / 2 ≤ 2) h.hp (frobNorm_nonneg _) (by norm_num)
    linarith
  have hX' : frobNorm (su2Log g' - su2Log g0) ≤ 2 * Kd * τ := by
    refine hl'.trans ?_
    have := mul_le_mul (by linarith : Real.pi / 2 ≤ 2) h.hq (frobNorm_nonneg _) (by norm_num)
    linarith
  have hX2 : frobNorm (su2Log g - su2Log g0) ≤ 1 / 2 := by linarith
  have hX2' : frobNorm (su2Log g' - su2Log g0) ≤ 1 / 2 := by linarith
  refine ⟨?_, hX, hX'⟩
  have hinv := even_exp_inv (su2Log g) (su2Log g') (su2Log g0) hX2 hX2' hE
  rw [exp_su2Log_coe g hne, exp_su2Log_coe g' hne', exp_su2Log_coe g0 hne0] at hinv
  have hEle : Real.exp (Real.sqrt 2 * frobNorm (su2Log g0)) ≤ 5 / 4 := by linarith
  have hE0 : 0 ≤ Real.exp (Real.sqrt 2 * frobNorm (su2Log g0)) := (Real.exp_pos _).le
  have hn1 := frobNorm_nonneg (su2Log g - su2Log g0)
  have hn2 := frobNorm_nonneg (su2Log g' - su2Log g0)
  have q1 : frobNorm (su2Log g - su2Log g0) ^ 2 ≤ (2 * Kd * τ) ^ 2 := pow_le_pow_left₀ hn1 hX 2
  have q2 : frobNorm (su2Log g' - su2Log g0) ^ 2 ≤ (2 * Kd * τ) ^ 2 := pow_le_pow_left₀ hn2 hX' 2
  have c1 : 2 * Real.sqrt 2 * Real.exp (Real.sqrt 2 * frobNorm (su2Log g0)) ≤ 15 / 4 := by
    have := mul_le_mul hs2 hEle hE0 (by norm_num); nlinarith
  have hsn : 0 ≤ frobNorm (su2Log g - su2Log g0) ^ 2 + frobNorm (su2Log g' - su2Log g0) ^ 2 := by positivity
  have c2 := mul_le_mul c1 (add_le_add q1 q2) hsn (by norm_num)
  have he := h.he
  have : (2 * Ke + 60 * Kd ^ 2) * τ ^ 2 = 2 * (Ke * τ ^ 2) + 60 * (Kd * τ) ^ 2 := by ring
  rw [this]
  nlinarith

/-! ## the base links `exp(±H)` around `1` -/

theorem EvQ.base (H : Mt) (τ : ℝ) (hH : frobNorm H ≤ τ) (hτ : τ ≤ 1 / 2) :
    EvQ (NormedSpace.exp H) (NormedSpace.exp (-H)) 1 6 4 τ := by
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h0 : frobNorm (0 : Mt) = 0 := fN_zero
  have hH0 := frobNorm_nonneg H
  have hτ0 : 0 ≤ τ := hH0.trans hH
  have hexp0 : NormedSpace.exp (0 : Mt) = 1 := NormedSpace.exp_zero
  have hE1 : Real.exp (Real.sqrt 2 * frobNorm (0 : Mt)) = 1 := by rw [h0, mul_zero, Real.exp_zero]
  have hX : frobNorm (H - 0) ≤ 1 / 2 := by rw [sub_zero]; linarith
  have hY : frobNorm (-H - 0) ≤ 1 / 2 := by rw [sub_zero, fN_neg]; linarith
  refine ⟨?_, ?_, ?_⟩
  · have hev := even_exp H (-H) 0 hX hY
    rw [hexp0, hE1] at hev
    have e1 : H + -H - 2 • (0 : Mt) = 0 := by simp
    rw [e1, h0, sub_zero, sub_zero, fN_neg] at hev
    have q : frobNorm H ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hH0 hH 2
    nlinarith
  · have hl := lip_exp H 0 hX
    rw [hexp0, hE1, sub_zero] at hl
    have q : frobNorm H ^ 2 ≤ τ * (1 / 2) := by nlinarith
    nlinarith
  · have hl := lip_exp (-H) 0 hY
    rw [hexp0, hE1, sub_zero, fN_neg] at hl
    have q : frobNorm H ^ 2 ≤ τ * (1 / 2) := by nlinarith
    nlinarith

/-! ## path holonomies -/

variable {L : PeriodicLatticeExtent}

theorem EvQ.hol (s : ℕ) (Vp Vm Vz : PeriodicLinkConfiguration SU2 L) (ke kd τ : ℝ) (hke : 0 ≤ ke) (hkd : 0 ≤ kd)
    (hτ : 0 ≤ τ) (hV : ∀ e, EvQ ((Vp e : SU2) : Mt) ((Vm e : SU2) : Mt) ((Vz e : SU2) : Mt) ke kd τ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L),
      EvQ ((coarsePathHolonomy s Vp y p : SU2) : Mt) ((coarsePathHolonomy s Vm y p : SU2) : Mt)
        ((coarsePathHolonomy s Vz y p : SU2) : Mt)
        (ke * p.length + 2 * kd ^ 2 * (p.length : ℝ) ^ 2) (kd * p.length) τ := by
  intro p
  induction p with
  | nil =>
      intro y
      have : EvQ ((1 : SU2) : Mt) ((1 : SU2) : Mt) ((1 : SU2) : Mt) 0 0 τ := EvQ.const1 1 τ
      simpa [coarsePathHolonomy] using this
  | cons μ rest ih =>
      intro y
      have h1 := (hV (y, μ)).mul (ih (coarseShift y s μ))
      have e1 : coarsePathHolonomy s Vp y (μ :: rest) = Vp (y, μ) * coarsePathHolonomy s Vp (coarseShift y s μ) rest := rfl
      have e2 : coarsePathHolonomy s Vm y (μ :: rest) = Vm (y, μ) * coarsePathHolonomy s Vm (coarseShift y s μ) rest := rfl
      have e3 : coarsePathHolonomy s Vz y (μ :: rest) = Vz (y, μ) * coarsePathHolonomy s Vz (coarseShift y s μ) rest := rfl
      rw [e1, e2, e3]
      refine h1.mono hτ ?_ ?_
      · simp only [List.length_cons]; push_cast
        have hn : (0 : ℝ) ≤ rest.length := Nat.cast_nonneg _
        nlinarith [mul_nonneg hke hn, mul_nonneg (sq_nonneg kd) hn]
      · simp only [List.length_cons]; push_cast; nlinarith

#print axioms fN_unitary_mul
#print axioms EvQ.add
#print axioms EvQ.sum
#print axioms EvQ.avg
#print axioms EvQ.mul
#print axioms EvQ.inv
#print axioms EvQ.exp
#print axioms EvQ.log
#print axioms EvQ.base
#print axioms EvQ.hol

end AdalyFormal.DLayer
