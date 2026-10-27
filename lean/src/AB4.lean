import AB3
/-!
# AB4 -- level-uniform abelian curvature blocking of the linearised tower (every `ell ≥ 1`)

`linT ell f l` is the `l`-fold blocked angle field.  If every fine curl satisfies `|curl| ≤ q0` and
`ell^n ∣ L ν + 1`, then for `l ≤ n` and every `y ∈ CoarseLattice L (ell^l)`:

  `|curlS (ell^l) (linT ell f l) y ν μ| ≤ (ell²)^l · q0`        (`linT_curl`)

— CMP98 Prop. 2 in the abelian sector with constant exactly 1 (no remainder).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.AbelianBlockingRate (blkAngle)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

/-- The linearised (angle) tower. -/
def linT (ell : ℕ) (f : PeriodicLatticeEdge L → ℝ) : ℕ → PeriodicLatticeEdge L → ℝ
  | 0 => f
  | l + 1 => blkAngle (ell ^ l) ell (linT ell f l)

/-- Plaquettes enclosed by a ladder based at an `s`-aligned point are `s`-aligned. -/
theorem ladPlaqs_aligned (s : ℕ) (hdvd : ∀ ρ, s ∣ L ρ + 1) (μ : Fin 3) (n : ℕ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), y ∈ CoarseLattice L s →
      ∀ t ∈ ladPlaqs s μ n y p, t.1 ∈ CoarseLattice L s := by
  have hr : ∀ (ν : Fin 3) (k : ℕ) (z : PeriodicLatticeSite L), z ∈ CoarseLattice L s →
      ∀ t ∈ rungPlaqs s ν μ z k, t.1 ∈ CoarseLattice L s := by
    intro ν k
    induction k with
    | zero => intro z _ t ht; simp [rungPlaqs] at ht
    | succ k ih =>
        intro z hz t ht
        rcases List.mem_cons.mp ht with h | h
        · rw [h]; exact hz
        · exact ih _ (coarseShift_mem_coarseLattice hdvd hz μ) t h
  intro p
  induction p with
  | nil => intro y _ t ht; simp [ladPlaqs] at ht
  | cons ν rest ih =>
      intro y hy t ht
      rcases List.mem_append.mp ht with h | h
      · exact hr ν n y hy t h
      · exact ih _ (coarseShift_mem_coarseLattice hdvd hy ν) t h

/-- A block site of an `s·ell`-aligned base point is `s`-aligned. -/
theorem block_aligned (s ell : ℕ) {y x : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L (s * ell)) (hx : x ∈ stepBlockOf y s ell) :
    x ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  have h := (mem_stepBlockOf.mp hx) ν
  have h1 : s ∣ (y ν).val := Nat.dvd_trans (Dvd.intro ell rfl) (Nat.dvd_of_mod_eq_zero (hy ν))
  have h2 : s ∣ (x ν).val := by
    have := Nat.dvd_add h1 h.2.2
    rwa [Nat.add_sub_cancel' h.1] at this
  exact Nat.mod_eq_zero_of_dvd h2

/-- **Level-uniform abelian curvature blocking.** -/
theorem linT_curl (ell : ℕ) (hell : 0 < ell) (f : PeriodicLatticeEdge L → ℝ) (q0 : ℝ)
    (h0 : ∀ y ν μ, |curlS 1 f y ν μ| ≤ q0) (n : ℕ) (hdvd : ∀ ρ, ell ^ n ∣ L ρ + 1) :
    ∀ l ≤ n, ∀ y ∈ CoarseLattice L (ell ^ l), ∀ ν μ : Fin 3,
      |curlS (ell ^ l) (linT ell f l) y ν μ| ≤ ((ell : ℝ) ^ 2) ^ l * q0 := by
  intro l
  induction l with
  | zero =>
      intro _ y _ ν μ
      show |curlS 1 f y ν μ| ≤ ((ell : ℝ) ^ 2) ^ 0 * q0
      rw [pow_zero, one_mul]; exact h0 y ν μ
  | succ k ih =>
      intro hk y hy ν μ
      have hs : 0 < ell ^ k := pow_pos hell k
      have hd1 : ∀ ρ, ell ^ k * ell ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (by rw [← pow_succ]; exact Nat.pow_dvd_pow ell hk) (hdvd ρ)
      have hd0 : ∀ ρ, ell ^ k ∣ L ρ + 1 := fun ρ =>
        Nat.dvd_trans (Nat.pow_dvd_pow ell (by omega)) (hdvd ρ)
      have hy' : y ∈ CoarseLattice L (ell ^ k * ell) := by rw [← pow_succ]; exact hy
      have hid := curl_blk_identity (ell ^ k) ell hs hell (linT ell f k) y ν μ hd1 hy'
      have hpow : ell ^ (k + 1) = ell ^ k * ell := pow_succ ell k
      show |curlS (ell ^ (k + 1)) (blkAngle (ell ^ k) ell (linT ell f k)) y ν μ| ≤ _
      rw [hpow, hid]
      set Q : ℝ := ((ell : ℝ) ^ 2) ^ k * q0
      have hbd : ∀ x ∈ stepBlockOf y (ell ^ k) ell,
          |((ell : ℝ) ^ 3)⁻¹ * ladA (ell ^ k) (linT ell f k) x (List.replicate ell ν) μ ell|
            ≤ ((ell : ℝ) ^ 3)⁻¹ * ((ell : ℝ) ^ 2 * Q) := by
        intro x hx
        have hxa := block_aligned (ell ^ k) ell hy' hx
        have hl := ladA_le (ell ^ k) (linT ell f k) μ ell Q (List.replicate ell ν) x
          (fun t ht => ih (by omega) t.1 (ladPlaqs_aligned (ell ^ k) hd0 μ ell _ x hxa t ht)
            t.2.1 t.2.2)
        rw [List.length_replicate] at hl
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((ell : ℝ) ^ 3)⁻¹)]
        refine mul_le_mul_of_nonneg_left (le_trans hl (le_of_eq (by ring))) (by positivity)
      have hfit := coarseLattice_mem_fits hd1 hy'
      have hcard := AdalyFormal.Balaban.QjComposite.card_stepBlockOf y (ell ^ k) ell hs hfit
      calc |∑ x ∈ stepBlockOf y (ell ^ k) ell,
            ((ell : ℝ) ^ 3)⁻¹ * ladA (ell ^ k) (linT ell f k) x (List.replicate ell ν) μ ell|
          ≤ ∑ x ∈ stepBlockOf y (ell ^ k) ell,
            |((ell : ℝ) ^ 3)⁻¹ * ladA (ell ^ k) (linT ell f k) x (List.replicate ell ν) μ ell| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x ∈ stepBlockOf y (ell ^ k) ell, ((ell : ℝ) ^ 3)⁻¹ * ((ell : ℝ) ^ 2 * Q) :=
            Finset.sum_le_sum hbd
        _ = ((ell : ℝ) ^ 2) ^ (k + 1) * q0 := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            push_cast
            have : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
            field_simp
            simp only [Q]
            ring

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.linT_curl
