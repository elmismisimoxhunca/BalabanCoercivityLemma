import NsCvO17

/-!
# CvO18 -- `Rsig` on transverse-constant direction-1 fields: the block sum (lane omega)

`FormF s f θ`: on the stride-`s` coarse lattice `θ(z,μ) = [μ=1] f(z₀)` (a sigma_3, direction-1, transverse-constant field).  For `y` coarse at stride `s*ell`:
`Rsig s ell θ (y,1) = Σ_{n<ell} f(y₀ + s n)` and `Rsig s ell θ (y,0) = Rsig s ell θ (y,2) = 0`.
Hence `FormF (s*ell) (f') (Rsig s ell θ)` with `f'(v) = Σ_{n<ell} f(v + s n)`: iterating, the level-`j` composite of the (raw) constraint operator on such a field is the
sum of `ell^j` consecutive slices.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf coarsePathEndpoint_cons)

variable {L : PeriodicLatticeExtent}

/-- on the stride-`s` coarse lattice `θ(z,μ) = [μ=1] f(z₀)`. -/
def FormF (s : ℕ) (f : ℕ → ℝ) (θ : PeriodicLatticeEdge L → ℝ) : Prop :=
  ∀ z : PeriodicLatticeSite L, Crs s z → ∀ μ : Fin 3, θ (z, μ) = if μ = 1 then f (z 0).val else 0

theorem pathAngG_rep_one {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {f : ℕ → ℝ} {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ) (n : ℕ) :
    ∀ z : PeriodicLatticeSite L, Crs s z → pathAngG s θ z (List.replicate n 1) = n * f (z 0).val := by
  induction n with
  | zero => intro z _; simp [pathAngG]
  | succ n ih =>
    intro z hz
    have h0 : (coarseShift z s 1) 0 = z 0 := coarseShift_apply_ne z s 1 0 (by decide)
    rw [List.replicate_succ, pathAngG, ih _ (Crs_shift hdiv hz 1 s dvd_rfl), hθ z hz 1, h0]
    simp only [if_true]; push_cast; ring

theorem pathAngG_rep_ne {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {f : ℕ → ℝ} {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ)
    (μ : Fin 3) (hμ : μ ≠ 1) (n : ℕ) :
    ∀ z : PeriodicLatticeSite L, Crs s z → pathAngG s θ z (List.replicate n μ) = 0 := by
  induction n with
  | zero => intro z _; simp [pathAngG]
  | succ n ih =>
    intro z hz
    rw [List.replicate_succ, pathAngG, ih _ (Crs_shift hdiv hz μ s dvd_rfl), hθ z hz μ, if_neg hμ]; ring

theorem pathAngG_gamma_f {s : ℕ} (hdiv : ∀ μ, s ∣ L μ + 1) {f : ℕ → ℝ} {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ)
    (z y x : PeriodicLatticeSite L) (hz : Crs s z) :
    pathAngG s θ z (coarseGammaPath s y x) =
      (((x 1 - (Function.update y 2 (x 2)) 1).val / s : ℕ) : ℝ) * f (z 0).val := by
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  have c2 := crs_endpoint_rep hdiv 2 (((x 2 - y 2).val) / s) z hz
  have c1 := crs_endpoint_rep hdiv 1 (((x 1 - (Function.update y 2 (x 2)) 1).val) / s) _ c2
  rw [pathAngG_append, pathAngG_rep_ne hdiv hθ 2 (by decide) _ z hz, pathAngG_append, pathAngG_rep_one hdiv hθ _ _ c2,
    pathAngG_rep_ne hdiv hθ 0 (by decide) _ _ c1]
  rw [endpoint_rep_ne s 2 0 (by decide)]
  ring


theorem sum_range_id_real (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem n1_eq {s ell : ℕ} {y x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    ((x 1 - (Function.update y 2 (x 2)) 1).val) / s = ((x 1).val - (y 1).val) / s := by
  have e1 : (Function.update y 2 (x 2)) 1 = y 1 := by simp [Function.update_of_ne]
  have h := mem_stepBlockOf.mp hx 1
  have hle : y 1 ≤ x 1 := by rw [Fin.le_def]; exact h.1
  rw [e1, Fin.coe_sub_iff_le.mpr hle]

theorem crs_of_mul {s ell : ℕ} {y : PeriodicLatticeSite L} (hy : Crs (s * ell) y) : Crs s y :=
  fun μ => dvd_trans (dvd_mul_right s ell) (hy μ)

theorem sAng_formF {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) (hdiv : ∀ μ, s * ell ∣ L μ + 1) {f : ℕ → ℝ}
    {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ) (z : PeriodicLatticeSite L) (hz : Crs (s * ell) z) :
    sAngG s ell θ z = f (z 0).val * (((ell : ℝ) - 1) / 2) := by
  have hdiv' : ∀ μ, s ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right s ell) (hdiv μ)
  have hfit : ∀ μ, (z μ).val + s * ell ≤ L μ + 1 := fun μ => crs_fit hdiv hz μ
  unfold sAngG
  have h1 : ∀ x ∈ stepBlockOf z s ell, pathAngG s θ z (coarseGammaPath s z x) =
      (fun n : ℕ => (n : ℝ) * f (z 0).val) (((x 1).val - (z 1).val) / s) := by
    intro x hx
    rw [pathAngG_gamma_f hdiv' hθ z z x (crs_of_mul hz), n1_eq hx]
  rw [Finset.sum_congr rfl h1, sum_block_dir z s ell hs hfit 1 (fun n : ℕ => (n : ℝ) * f (z 0).val)]
  simp only [← Finset.sum_mul, sum_range_id_real]
  have hl : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  field_simp


variable {s ell : ℕ}

theorem hfit_of {hdiv : ∀ μ, s * ell ∣ L μ + 1} {y : PeriodicLatticeSite L} (hy : Crs (s * ell) y) (μ : Fin 3) :
    (y μ).val + s * ell ≤ L μ + 1 := crs_fit hdiv hy μ

theorem crs_cplus (hdiv : ∀ μ, s * ell ∣ L μ + 1) {y : PeriodicLatticeSite L} (hy : Crs (s * ell) y) (μ : Fin 3) :
    Crs (s * ell) (cPlusS s ell (y, μ)) := by
  rw [cPlusS_eq]; exact Crs_shift hdiv hy μ _ dvd_rfl

theorem blockAng_formF_one (hs : 0 < s) (hell : 0 < ell) (hdiv : ∀ μ, s * ell ∣ L μ + 1) {f : ℕ → ℝ}
    {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ) (y : PeriodicLatticeSite L) (hy : Crs (s * ell) y) :
    blockAngG s ell θ y 1 = ∑ n ∈ Finset.range ell, f ((y 0).val + s * n) := by
  have hdiv' : ∀ μ, s ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right s ell) (hdiv μ)
  have hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1 := fun μ => crs_fit hdiv hy μ
  have hys : Crs s y := crs_of_mul hy
  have hcp0 : (cPlusS s ell (y, 1)) 0 = y 0 := by rw [cPlusS_eq]; exact coarseShift_apply_ne y _ 1 0 (by decide)
  have hcps : Crs s (cPlusS s ell (y, 1)) := crs_of_mul (crs_cplus hdiv hy 1)
  have hl : ∀ x ∈ stepBlockOf y s ell, loopAngG s ell θ y 1 x = (ell : ℝ) * (f ((y 0).val + s * (((x 0).val - (y 0).val) / s)) - f (y 0).val) := by
    intro x hx
    have hxs : Crs s x := crs_of_mem_block hys hx
    unfold loopAngG
    rw [pathAngG_gamma_f hdiv' hθ y y x hys, pathAngG_gamma_f hdiv' hθ _ y x hcps, pathAngG_rep_one hdiv' hθ _ x hxs,
      pathAngG_rep_one hdiv' hθ _ y hys, hcp0]
    have hx0 : (x 0).val = (y 0).val + s * ((((x 0).val - (y 0).val) / s)) := by
      have h := mem_stepBlockOf.mp hx 0
      rw [Nat.mul_div_cancel' h.2.2]; have := h.1; omega
    rw [← hx0]; ring
  unfold blockAngG
  rw [Finset.sum_congr rfl hl, pathAngG_rep_one hdiv' hθ _ y hys, ← Finset.mul_sum]
  rw [sum_block_dir y s ell hs hfit 0 (fun n => f ((y 0).val + s * n) - f (y 0).val), Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hl' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  field_simp
  ring



theorem blockAng_formF_zero (hs : 0 < s) (hell : 0 < ell) (hdiv : ∀ μ, s * ell ∣ L μ + 1) {f : ℕ → ℝ}
    {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ) (y : PeriodicLatticeSite L) (hy : Crs (s * ell) y) :
    blockAngG s ell θ y 0 = (((ell : ℝ) - 1) / 2) * (f (y 0).val - f (((cPlusS s ell (y, 0)) 0).val)) := by
  have hdiv' : ∀ μ, s ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right s ell) (hdiv μ)
  have hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1 := fun μ => crs_fit hdiv hy μ
  have hys : Crs s y := crs_of_mul hy
  have hcps : Crs s (cPlusS s ell (y, 0)) := crs_of_mul (crs_cplus hdiv hy 0)
  have hl : ∀ x ∈ stepBlockOf y s ell, loopAngG s ell θ y 0 x =
      (fun n : ℕ => (n : ℝ) * (f (y 0).val - f (((cPlusS s ell (y, 0)) 0).val))) (((x 1).val - (y 1).val) / s) := by
    intro x hx
    have hxs : Crs s x := crs_of_mem_block hys hx
    unfold loopAngG
    rw [pathAngG_gamma_f hdiv' hθ y y x hys, pathAngG_gamma_f hdiv' hθ _ y x hcps, pathAngG_rep_ne hdiv' hθ 0 (by decide) _ x hxs,
      pathAngG_rep_ne hdiv' hθ 0 (by decide) _ y hys, n1_eq hx]
    ring
  unfold blockAngG
  rw [Finset.sum_congr rfl hl, pathAngG_rep_ne hdiv' hθ 0 (by decide) _ y hys,
    sum_block_dir y s ell hs hfit 1 (fun n : ℕ => (n : ℝ) * (f (y 0).val - f (((cPlusS s ell (y, 0)) 0).val)))]
  simp only [← Finset.sum_mul, sum_range_id_real]
  have hl' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  field_simp
  ring

theorem blockAng_formF_two (hs : 0 < s) (hell : 0 < ell) (hdiv : ∀ μ, s * ell ∣ L μ + 1) {f : ℕ → ℝ}
    {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ) (y : PeriodicLatticeSite L) (hy : Crs (s * ell) y) :
    blockAngG s ell θ y 2 = 0 := by
  have hdiv' : ∀ μ, s ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right s ell) (hdiv μ)
  have hys : Crs s y := crs_of_mul hy
  have hcp0 : (cPlusS s ell (y, 2)) 0 = y 0 := by rw [cPlusS_eq]; exact coarseShift_apply_ne y _ 2 0 (by decide)
  have hcps : Crs s (cPlusS s ell (y, 2)) := crs_of_mul (crs_cplus hdiv hy 2)
  have hl : ∀ x ∈ stepBlockOf y s ell, loopAngG s ell θ y 2 x = 0 := by
    intro x hx
    have hxs : Crs s x := crs_of_mem_block hys hx
    unfold loopAngG
    rw [pathAngG_gamma_f hdiv' hθ y y x hys, pathAngG_gamma_f hdiv' hθ _ y x hcps, pathAngG_rep_ne hdiv' hθ 2 (by decide) _ x hxs,
      pathAngG_rep_ne hdiv' hθ 2 (by decide) _ y hys, hcp0]
    ring
  unfold blockAngG
  rw [Finset.sum_congr rfl hl, pathAngG_rep_ne hdiv' hθ 2 (by decide) _ y hys]
  simp

/-- **the raw one-step map on a FormF field**: the block sum in direction `1`, nothing in directions `0, 2`. -/
theorem Rsig_formF (hs : 0 < s) (hell : 0 < ell) (hdiv : ∀ μ, s * ell ∣ L μ + 1) {f : ℕ → ℝ}
    {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ) (y : PeriodicLatticeSite L) (hy : Crs (s * ell) y) (μ : Fin 3) :
    Rsig s ell θ (y, μ) = if μ = 1 then ∑ n ∈ Finset.range ell, f ((y 0).val + s * n) else 0 := by
  have hcpc : Crs (s * ell) (cPlusS s ell (y, μ)) := crs_cplus hdiv hy μ
  unfold Rsig
  simp only []
  rw [sAng_formF hs hell hdiv hθ y hy, sAng_formF hs hell hdiv hθ _ hcpc]
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · rw [blockAng_formF_zero hs hell hdiv hθ y hy]
    simp only [if_neg (show ¬ ((0 : Fin 3) = 1) by decide)]
    ring
  · rw [blockAng_formF_one hs hell hdiv hθ y hy]
    have hcp0 : (cPlusS s ell (y, 1)) 0 = y 0 := by rw [cPlusS_eq]; exact coarseShift_apply_ne y _ 1 0 (by decide)
    simp only [if_true, hcp0]
    ring
  · rw [blockAng_formF_two hs hell hdiv hθ y hy]
    have hcp0 : (cPlusS s ell (y, 2)) 0 = y 0 := by rw [cPlusS_eq]; exact coarseShift_apply_ne y _ 2 0 (by decide)
    simp only [if_neg (show ¬ ((2 : Fin 3) = 1) by decide), hcp0]
    ring

/-- the output is again a FormF field on the next coarse lattice. -/
theorem formF_Rsig (hs : 0 < s) (hell : 0 < ell) (hdiv : ∀ μ, s * ell ∣ L μ + 1) {f : ℕ → ℝ}
    {θ : PeriodicLatticeEdge L → ℝ} (hθ : FormF s f θ) :
    FormF (s * ell) (fun v => ∑ n ∈ Finset.range ell, f (v + s * n)) (Rsig s ell θ) := by
  intro y hy μ
  rw [Rsig_formF hs hell hdiv hθ y hy μ]

#print axioms blockAng_formF_zero
#print axioms blockAng_formF_two
#print axioms Rsig_formF
#print axioms formF_Rsig

end AdalyFormal.CoverOmega
