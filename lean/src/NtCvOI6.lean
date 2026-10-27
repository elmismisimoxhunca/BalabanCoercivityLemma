import NtCvOI5

/-!
# CvOI6 -- `ginv_eq_Wt`: a saddle of the chain form gives `ginvProf f = Wt rho_v` on every slice (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open Finset
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)

variable {ell M R : ℕ}

/-- the row multiplier: `(L e)_x` for any slice `x` of the row. -/
theorem BF_single_rowMu (hg : NGeo ell M R) (Cc : ℕ) (c : ℝ) {e : Fin (nN ell M R) → ℝ}
    (hrad : ∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → BF Cc c e d = 0) (x : Fin (nN ell M R)) :
    BF Cc c e (Pi.single x 1) = rowMu Cc c e (stN ell M R) (rowOfN ell M R x.val) := by
  obtain ⟨hiR, hs1, hs2⟩ := rowOfN_spec hg x.2
  set i := rowOfN ell M R x.val with hi
  have hlt : stN ell M R i < nN ell M R := by
    have := stN_strictMono hg (show i < RN hg from hiR) |>.trans_le (by rw [stN_RN hg])
    exact this
  have hrow := (nested_rowGeom hg).row
  have hx0 : rowOfN ell M R (stN ell M R i) = i := by
    rw [hrow i hiR (stN ell M R i) hlt]
    refine ⟨le_rfl, ?_⟩
    have := (nested_rowGeom hg).ln1 i hiR
    omega
  have := chain_mult_const (rowOfN ell M R) Cc c e hrad x ⟨stN ell M R i, hlt⟩ (by show rowOfN ell M R x.val = rowOfN ell M R (stN ell M R i); rw [hx0])
  rw [this]
  unfold rowMu; rw [dif_pos hlt]

/-- the multiplier profile. -/
noncomputable def rhoV (ell M R : ℕ) (Cc : ℕ) (c a : ℝ) (e : Fin (nN ell M R) → ℝ) : ℕ → ℕ → ℝ :=
  fun j r => (ell : ℝ) ^ (3 * j) * rowMu Cc c e (stN ell M R) (rowOfN ell M R (r - neP0 ell M R)) + a * fSum ell j (fe (neP0 ell M R) e) r

theorem ginv_eq_Wt (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (e : Fin (nN ell M R) → ℝ)
    (hrad : ∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → BF (neC ell M R - neP0 ell M R) (Real.cos t) e d = 0)
    (v : ℕ) (hv : v ≤ scaleUp ell 2 (neLu M R) 0) :
    ginvProf ell (isRowN ell M R) (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0) (neC ell M R) t a
        (fe (neP0 ell M R) e) v =
      Wt ell (isRowN ell M R) (rhoV ell M R (neC ell M R - neP0 ell M R) (Real.cos t) a e) v := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  unfold ginvProf
  by_cases hvI : neP0 ell M R ≤ v ∧ v < neQ0 ell M R
  · -- inside: one row
    have hx : v - neP0 ell M R < nN ell M R := by unfold nN; omega
    set x : Fin (nN ell M R) := ⟨v - neP0 ell M R, hx⟩ with hxdef
    have hvx : v = neP0 ell M R + x.val := by simp [hxdef]; omega
    have hzp : zprof (scaleUp ell 2 (neLu M R) 0) (omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0) (neC ell M R) t)
        (fe (neP0 ell M R) e) v = rowMu (neC ell M R - neP0 ell M R) (Real.cos t) e (stN ell M R) (rowOfN ell M R x.val) := by
      rw [hvx, zprof_eq_BF hell3 hdvd hM hR t e x]
      exact BF_single_rowMu hg _ _ hrad x
    rw [hzp, Wt_single hg hvI, Wt_single hg hvI]
    have hPv : neP0 ell M R + (v - neP0 ell M R) = v := by omega
    have hxv : x.val = v - neP0 ell M R := rfl
    have hrs := (chain_row_level hg hx).1
    rw [hPv] at hrs
    set j := levN ell M R v with hj
    have hiR := (rowOfN_spec hg hx).1
    have hlt : stN ell M R (rowOfN ell M R (v - neP0 ell M R)) < nN ell M R := by
      have := stN_strictMono hg (show rowOfN ell M R (v - neP0 ell M R) < RN hg from hiR) |>.trans_le (by rw [stN_RN hg])
      exact this
    have hrow : rowOfN ell M R (rstartN ell M R v - neP0 ell M R) = rowOfN ell M R x.val := by
      rw [← hrs]; simp only [Nat.add_sub_cancel_left, hxv]
      rw [(nested_rowGeom hg).row _ hiR (stN ell M R (rowOfN ell M R (v - neP0 ell M R))) hlt]
      exact ⟨le_rfl, by have := (nested_rowGeom hg).ln1 _ hiR; omega⟩
    -- the mass part
    unfold rhoV
    rw [hrow]
    have hp : (ell : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hell.ne')
    have e3 : (ell : ℝ) ^ (3 * j) = ((ell : ℝ) ^ j) * (((ell : ℝ) ^ 2) ^ j) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e3]
    have hp2 : (((ell : ℝ) ^ 2) ^ j) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hell.ne'))
    have hq1 : ((ell : ℝ) ^ j)⁻¹ * (ell : ℝ) ^ j = 1 := inv_mul_cancel₀ hp
    have hq2 : (((ell : ℝ) ^ 2)⁻¹) ^ j * ((ell : ℝ) ^ 2) ^ j = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hell.ne')), one_pow]
    set A := ((ell : ℝ) ^ j)⁻¹ with hA
    set B := (((ell : ℝ) ^ 2)⁻¹) ^ j with hB
    linear_combination (-(rowMu (neC ell M R - neP0 ell M R) (Real.cos t) e (stN ell M R) (rowOfN ell M R x.val))) * (B * ((ell : ℝ) ^ 2) ^ j * hq1 + hq2)
  · -- outside: both zero
    have hJ : ¬ (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) v := hvI
    rw [zprof_supp _ _ _ t _ v hv hJ]
    have hz : ∀ ρ : ℕ → ℕ → ℝ, Wt ell (isRowN ell M R) ρ v = 0 := by
      intro ρ
      unfold Wt
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hj2 : j ≤ 2 := by have := Finset.mem_range.mp hj; omega
      rw [if_neg (fun h => hvI (hrowJ_nested hg hj2 v h))]; ring
    rw [hz, hz]; ring

#print axioms ginv_eq_Wt

end AdalyFormal.CoverOmega
