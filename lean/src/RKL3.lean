import RKL2
/-!
# RKL3 -- the composite of the truncated linear blockings grows SLOWER than `(ell²)^m`, at every bond.

`Tcomp ell a m = blkM_{ell^{a+m-1}} ∘ … ∘ blkM_{ell^a}` (levels `a … a+m−1`, the tree's truncated blocks at every bond).
`Tcomp_le`: if `‖f‖ ≤ M` on every bond, then `‖Tcomp ell a m f‖ ≤ 7 λ^m M` on every bond, for every
`λ ≥ ell + Emax`, `Emax = 3(ell−1)²/ell`.  (`lamK ell := ell + Emax < ell²` for every `ell ≥ 2`: `lamK_lt_sq`.)
Mechanism: `Tcomp a m f = Ā_m + grad Λ_m + R_m` (RKL1 decomposition iterated), `‖Ā_m‖ ≤ ell^m M`, `‖grad Λ_m‖ ≤ 6 ell^m M`,
`R_m = Σ_{i<m} Tcomp (a+i+1) (m−1−i) (Es (Ā_i))` (mismatch terms, each `≤ Emax ell^i M`, propagated by shorter composites).
Kernel-checked; standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.RegBgKU
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.CurvBlock (blkM)

variable {L : PeriodicLatticeExtent}

/-- composite of the linear truncated blockings at levels `a, …, a+m−1`. -/
def Tcomp (ell a : ℕ) : ℕ → Fld L → Fld L
  | 0, f => f
  | m + 1, f => blkM (ell ^ (a + m)) ell (Tcomp ell a m f)

theorem Tcomp_add (ell a : ℕ) : ∀ (m : ℕ) (f g : Fld L), Tcomp ell a m (f + g) = Tcomp ell a m f + Tcomp ell a m g := by
  intro m; induction m with
  | zero => intro f g; rfl
  | succ m ih => intro f g; simp only [Tcomp, ih, blkM_add]

theorem Tcomp_sub (ell a : ℕ) : ∀ (m : ℕ) (f g : Fld L), Tcomp ell a m (f - g) = Tcomp ell a m f - Tcomp ell a m g := by
  intro m; induction m with
  | zero => intro f g; rfl
  | succ m ih => intro f g; simp only [Tcomp, ih, blkM_sub]

theorem Tcomp_zero (ell a : ℕ) : ∀ (m : ℕ), Tcomp ell a m (0 : Fld L) = 0 := by
  intro m; induction m with
  | zero => rfl
  | succ m ih => simp only [Tcomp, ih, blkM_zero]

theorem Tcomp_sum (ell a m : ℕ) {ι : Type*} (S : Finset ι) (F : ι → Fld L) :
    Tcomp ell a m (∑ i ∈ S, F i) = ∑ i ∈ S, Tcomp ell a m (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Tcomp_zero]
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Tcomp_add, ih]

theorem blkM_sum (s ell : ℕ) {ι : Type*} (S : Finset ι) (F : ι → Fld L) :
    blkM s ell (∑ i ∈ S, F i) = ∑ i ∈ S, blkM s ell (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [blkM_zero]
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, blkM_add, ih]

theorem grad_add (s : ℕ) (Λ Λ' : PeriodicLatticeSite L → M2) : grad s (Λ + Λ') = grad s Λ + grad s Λ' := by
  funext b; simp only [grad, Pi.add_apply]; abel

theorem grad_zero (s : ℕ) : grad s (0 : PeriodicLatticeSite L → M2) = 0 := by
  funext b; simp [grad]

/-- the straight-line averages `Ā_i`. -/
def Abar (ell a : ℕ) (f : Fld L) : ℕ → Fld L
  | 0 => f
  | i + 1 => avgM (ell ^ (a + i)) ell (Abar ell a f i)

/-- the accumulated gauge function `Λ_i`. -/
def Lam (ell a : ℕ) (f : Fld L) : ℕ → PeriodicLatticeSite L → M2
  | 0 => 0
  | i + 1 => Lam ell a f i + Gs (ell ^ (a + i)) ell (Abar ell a f i)

/-- the mismatch remainder `R_i`. -/
def Rem (ell a : ℕ) (f : Fld L) : ℕ → Fld L
  | 0 => 0
  | i + 1 => blkM (ell ^ (a + i)) ell (Rem ell a f i) + Es (ell ^ (a + i)) ell (Abar ell a f i)

theorem Tcomp_decomp (ell a : ℕ) (f : Fld L) :
    ∀ m, Tcomp ell a m f = Abar ell a f m + grad (ell ^ (a + m)) (Lam ell a f m) + Rem ell a f m := by
  intro m; induction m with
  | zero => simp [Tcomp, Abar, Lam, Rem, grad_zero]
  | succ m ih =>
      have hs : ell ^ (a + (m + 1)) = ell ^ (a + m) * ell := by rw [← Nat.add_assoc, pow_succ]
      show blkM (ell ^ (a + m)) ell (Tcomp ell a m f) = _
      rw [ih, blkM_add, blkM_add, blkM_grad]
      funext b
      simp only [Pi.add_apply, Abar, Lam, Rem, grad_add, hs]
      rw [blkM_decomp]
      abel

theorem Rem_unroll (ell a : ℕ) (f : Fld L) :
    ∀ m, Rem ell a f m = ∑ i ∈ Finset.range m, Tcomp ell (a + i + 1) (m - 1 - i) (Es (ell ^ (a + i)) ell (Abar ell a f i)) := by
  intro m; induction m with
  | zero => simp [Rem]
  | succ m ih =>
      show blkM (ell ^ (a + m)) ell (Rem ell a f m) + Es (ell ^ (a + m)) ell (Abar ell a f m) = _
      rw [ih, blkM_sum, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        have e1 : m + 1 - 1 - i = (m - 1 - i) + 1 := by omega
        have e2 : a + i + 1 + (m - 1 - i) = a + m := by omega
        rw [e1]; show _ = blkM (ell ^ (a + i + 1 + (m - 1 - i))) ell _; rw [e2]
      · have e3 : m + 1 - 1 - m = 0 := by omega
        rw [e3]; rfl

theorem Abar_le (ell a : ℕ) (hell : 0 < ell) (f : Fld L) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ b, frobNorm (f b) ≤ M) :
    ∀ i b, frobNorm (Abar ell a f i b) ≤ (ell : ℝ) ^ i * M := by
  intro i; induction i with
  | zero => intro b; show frobNorm (f b) ≤ (ell : ℝ) ^ 0 * M; rw [pow_zero, one_mul]; exact hf b
  | succ i ih =>
      intro b
      have h := avgM_le (ell ^ (a + i)) ell (by positivity) hell (Abar ell a f i) ((ell : ℝ) ^ i * M) (by positivity) ih b
      simp only [Abar]; rw [pow_succ]; linarith

theorem Lam_le (ell a : ℕ) (hell : 0 < ell) (f : Fld L) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ b, frobNorm (f b) ≤ M) :
    ∀ i z, frobNorm (Lam ell a f i z) ≤ 3 * ((ell : ℝ) ^ i - 1) * M := by
  intro i; induction i with
  | zero => intro z; simp [Lam, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
  | succ i ih =>
      intro z
      have h1 := Gs_le (ell ^ (a + i)) ell (by positivity) hell (Abar ell a f i) ((ell : ℝ) ^ i * M) (by positivity)
        (Abar_le ell a hell f M hM hf i) z
      have h2 := frob_add (Lam ell a f i z) (Gs (ell ^ (a + i)) ell (Abar ell a f i) z)
      simp only [Lam, Pi.add_apply]
      have := ih z
      rw [pow_succ]; nlinarith

/-- the mismatch constant `Emax = 3(ell−1)²/ell`. -/
def Emax (ell : ℕ) : ℝ := 3 * ((ell : ℝ) - 1) ^ 2 / ell

/-- the growth rate of the composite. -/
def lamK (ell : ℕ) : ℝ := ell + Emax ell

theorem lamK_lt_sq (ell : ℕ) (hell : 2 ≤ ell) : lamK ell < (ell : ℝ) ^ 2 := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl0 : (0 : ℝ) < ell := by linarith
  unfold lamK Emax
  rw [← sub_pos]
  have : (ell : ℝ) ^ 2 - (ell + 3 * ((ell : ℝ) - 1) ^ 2 / ell)
      = ((ell : ℝ) ^ 3 - 4 * (ell : ℝ) ^ 2 + 6 * ell - 3) / ell := by field_simp; ring
  rw [this]
  apply div_pos _ hl0
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hl), mul_nonneg (mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hl)) (sub_nonneg.mpr hl)]

theorem geom_bound (lam l E : ℝ) (hl : 0 ≤ l) (hE : 0 ≤ E) (h : l + E ≤ lam) :
    ∀ m : ℕ, l ^ m + E * ∑ i ∈ Finset.range m, lam ^ (m - 1 - i) * l ^ i ≤ lam ^ m := by
  have hlam : 0 ≤ lam := by linarith
  intro m; induction m with
  | zero => simp
  | succ m ih =>
      have hs : ∑ i ∈ Finset.range (m + 1), lam ^ (m + 1 - 1 - i) * l ^ i
          = lam * ∑ i ∈ Finset.range m, lam ^ (m - 1 - i) * l ^ i + l ^ m := by
        rw [Finset.sum_range_succ, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi' := Finset.mem_range.mp hi
          rw [show m + 1 - 1 - i = (m - 1 - i) + 1 by omega, pow_succ]; ring
        · rw [show m + 1 - 1 - m = 0 by omega]; ring
      rw [hs, pow_succ, pow_succ]
      have h1 := mul_le_mul_of_nonneg_left ih hlam
      have h2 : l ^ m * l + E * l ^ m ≤ lam * l ^ m := by
        have := mul_le_mul_of_nonneg_left h (pow_nonneg hl m); nlinarith
      nlinarith

/-- **Composite norm bound (every bond, every level offset `a`).** -/
theorem Tcomp_le (ell : ℕ) (hell : 0 < ell) (lam : ℝ) (hlam : lamK ell ≤ lam) :
    ∀ (m a : ℕ) (f : Fld L) (M : ℝ), 0 ≤ M → (∀ b, frobNorm (f b) ≤ M) →
      ∀ b, frobNorm (Tcomp ell a m f b) ≤ 7 * lam ^ m * M := by
  have hl0 : (0 : ℝ) < ell := by exact_mod_cast hell
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hE : 0 ≤ Emax ell := by unfold Emax; positivity
  have hlam0 : 0 ≤ lam := by unfold lamK at hlam; linarith
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro a f M hM hf b
  rw [Tcomp_decomp ell a f m]
  have hA := Abar_le ell a hell f M hM hf m b
  have hΛ := Lam_le ell a hell f M hM hf m
  have hG := grad_le (ell ^ (a + m)) (Lam ell a f m) (3 * ((ell : ℝ) ^ m - 1) * M) hΛ b
  have hR : frobNorm (Rem ell a f m b)
      ≤ 7 * M * Emax ell * ∑ i ∈ Finset.range m, lam ^ (m - 1 - i) * (ell : ℝ) ^ i := by
    rw [Rem_unroll, Finset.sum_apply]
    refine (frob_sum _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    have hEi : ∀ c, frobNorm (Es (ell ^ (a + i)) ell (Abar ell a f i) c) ≤ Emax ell * ((ell : ℝ) ^ i * M) := by
      intro c
      have := Es_le (ell ^ (a + i)) ell (by positivity) hell (Abar ell a f i) ((ell : ℝ) ^ i * M) (by positivity)
        (Abar_le ell a hell f M hM hf i) c
      unfold Emax; exact this
    have := IH (m - 1 - i) (by omega) (a + i + 1) _ (Emax ell * ((ell : ℝ) ^ i * M)) (by positivity) hEi b
    calc _ ≤ 7 * lam ^ (m - 1 - i) * (Emax ell * ((ell : ℝ) ^ i * M)) := this
      _ = 7 * M * Emax ell * (lam ^ (m - 1 - i) * (ell : ℝ) ^ i) := by ring
  have hgeo := geom_bound lam ell (Emax ell) hl0.le hE hlam m
  have h1 := frob_add (Abar ell a f m b + grad (ell ^ (a + m)) (Lam ell a f m) b) (Rem ell a f m b)
  have h2 := frob_add (Abar ell a f m b) (grad (ell ^ (a + m)) (Lam ell a f m) b)
  simp only [Pi.add_apply]
  have hpow : 1 ≤ (ell : ℝ) ^ m := one_le_pow₀ hl1
  nlinarith [mul_le_mul_of_nonneg_left hgeo (by positivity : (0 : ℝ) ≤ 7 * M)]

#print axioms Tcomp_decomp
#print axioms Rem_unroll
#print axioms lamK_lt_sq
#print axioms Tcomp_le

#print axioms Tcomp_add
#print axioms Tcomp_sub
#print axioms Tcomp_zero
#print axioms Tcomp_sum
#print axioms blkM_sum
#print axioms Abar_le
#print axioms Lam_le
#print axioms geom_bound
#print axioms grad_add
#print axioms grad_zero
end AdalyFormal.RegBgKU
