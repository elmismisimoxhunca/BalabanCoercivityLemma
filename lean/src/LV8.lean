import LV7

/-!
# LV8 -- the bounds on `Sx`, `Bx`, `Dx`, `Lx`

Row energies (`n = ℓ^j`, `N = ℓ^j ℓ`): `Gs = Σ_small n⁻¹‖ΔΦs‖²`, `Gb = Σ_big N⁻¹‖ΔΦB‖²`, `Fsm = Σ_small n‖Fs‖²`,
`Fbg = Σ_big N‖FB‖²`.
* `bound_S` : `2|Sx| ≤ α Gs + Fsm/α`; `bound_B` : `2|Bx| ≤ t Gb + Fbg/t`.
* `bound_D` : `2|Dx| ≤ ℓ² (τ · DΦ + Fbg/τ)` with `DΦ ≤ (2/ℓ²) Gs` (`bound_DΦ`, directional layer estimate).
* `bound_L` : `2|Lx| ≤ ρ · LΦ + LF/ρ` with `LΦ ≤ 54 ℓ⁴ Gs` (`bound_LΦ`, cube Poincaré) and
  `LF ≤ 288 ℓ⁴ Σ_μ E1(c_μ)` (`bound_LF`, flux variation).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.FlatCoercivity (eU)
open AdalyFormal.StatementLane (BlockClosed)

variable {L : PeriodicLatticeExtent}

/-! ## generic sum bounds -/

theorem two_abs_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ) (a b : ι → κ → ℝ)
    (h : ∀ i ∈ s, ∀ k ∈ t, 2 * |a i k| ≤ b i k) :
    2 * |∑ i ∈ s, ∑ k ∈ t, a i k| ≤ ∑ i ∈ s, ∑ k ∈ t, b i k := by
  have h1 : |∑ i ∈ s, ∑ k ∈ t, a i k| ≤ ∑ i ∈ s, ∑ k ∈ t, |a i k| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  have h2 : ∑ i ∈ s, ∑ k ∈ t, 2 * |a i k| ≤ ∑ i ∈ s, ∑ k ∈ t, b i k :=
    Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun k hk => h i hi k hk))
  simp only [← Finset.mul_sum] at h2
  linarith

theorem dev_avg {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset ι) (K : ℝ)
    (hK : (s.card : ℝ) = K) (hKp : 0 < K) (x : ι → E) (k : ι) :
    ‖x k - K⁻¹ • ∑ k' ∈ s, x k'‖ ^ 2 ≤ K⁻¹ * ∑ k' ∈ s, ‖x k - x k'‖ ^ 2 := by
  have e : x k - K⁻¹ • ∑ k' ∈ s, x k' = K⁻¹ • ∑ k' ∈ s, (x k - x k') := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, hK, smul_sub, smul_smul,
      inv_mul_cancel₀ hKp.ne', one_smul]
  rw [e]
  exact avg_sq_le s K hK hKp _

theorem onLat_mul_smul {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ L μ + 1) (r : ℕ) (μ : Fin 3) :
    OnLatN m ((m * r) • eU L μ) := by
  intro ν
  rw [Pi.smul_apply, AdalyFormal.FlatCoercivity.fin_val_nsmul]
  exact (Nat.dvd_mod_iff (hdvd ν)).mpr (dvd_mul_of_dvd_left (dvd_mul_right m r) _)

theorem two_abs_ite (C : Prop) [Decidable C] (x y : ℝ) (h : C → 2 * |x| ≤ y) :
    2 * |(if C then x else 0)| ≤ (if C then y else 0) := by
  split_ifs with hC
  · exact h hC
  · simp

theorem two_abs_ite_sub (A B : Prop) [Decidable A] [Decidable B] (a b a' b' : ℝ)
    (ha : A → 2 * |a| ≤ a') (hb : B → 2 * |b| ≤ b') :
    2 * |(if A then a else 0) - (if B then b else 0)| ≤ (if A then a' else 0) + (if B then b' else 0) := by
  have h1 := two_abs_ite A a a' ha
  have h2 := two_abs_ite B b b' hb
  have h3 := abs_sub (if A then a else 0) (if B then b else 0)
  linarith

theorem sum_lin2 {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f g h : ι → κ → ℝ) (A B : ℝ)
    (hpt : ∀ i k, f i k = A * g i k + h i k * B) :
    ∑ i ∈ s, ∑ k ∈ t, f i k = A * ∑ i ∈ s, ∑ k ∈ t, g i k + (∑ i ∈ s, ∑ k ∈ t, h i k) * B := by
  simp only [hpt, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]

theorem two_abs_inner_sum {ι : Type*} (s : Finset ι) (x y : ι → SuTwo) (p : ℝ) (hp : 0 < p) :
    2 * |∑ k ∈ s, ⟪x k, y k⟫| ≤ ∑ k ∈ s, (p * ‖x k‖ ^ 2 + ‖y k‖ ^ 2 / p) := by
  have h1 := Finset.abs_sum_le_sum_abs (fun k => ⟪x k, y k⟫) s
  have h2 : ∑ k ∈ s, 2 * |⟪x k, y k⟫| ≤ ∑ k ∈ s, (p * ‖x k‖ ^ 2 + ‖y k‖ ^ 2 / p) :=
    Finset.sum_le_sum (fun k _ => amgm (x k) (y k) p hp)
  rw [← Finset.mul_sum] at h2
  linarith

/-! ## the row energies -/

section defs
variable (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (φ : PeriodicLatticeSite L → SuTwo) (c : Bond L → SuTwo)

open Classical in
noncomputable def Gs : ℝ :=
  ∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
    ((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (z + ell ^ j • eU L μ) - Phm (ell ^ j) φ z‖ ^ 2 else 0)

open Classical in
noncomputable def Gb : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
    ((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j * ell) φ (Z + (ell ^ j * ell) • eU L μ) - Phm (ell ^ j * ell) φ Z‖ ^ 2
    else 0)

open Classical in
noncomputable def Fsm : ℝ :=
  ∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j), (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
    ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c z μ‖ ^ 2 else 0)

open Classical in
noncomputable def Fbg : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
    ((ell ^ j * ell : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2 else 0)

open Classical in
noncomputable def DPh : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then
    ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
        ((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Ptop ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)
      + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
        ((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)) else 0)

open Classical in
noncomputable def FBs : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then
    ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
        ((ell ^ j * ell : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2 else 0)
      + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
        ((ell ^ j * ell : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2 else 0))
    else 0)

open Classical in
noncomputable def LPh : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then
    ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
        ((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ) - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)
      + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
        ((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)) else 0)

open Classical in
noncomputable def LF : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then
    ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
        ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ
          - Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2 else 0)
      + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
        ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
          - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2 else 0)) else 0)

end defs

/-! ## the four AM-GM bounds -/

section amgm_bounds
variable {ell j : ℕ} (hell : 0 < ell) (Rg : Set (PeriodicLatticeSite L)) (φ : PeriodicLatticeSite L → SuTwo)
  (c : Bond L → SuTwo)
include hell

theorem bound_S (α : ℝ) (hα : 0 < α) :
    2 * |Sx ell j Rg φ c| ≤ α * Gs ell j Rg φ + Fsm ell j Rg c / α := by
  classical
  have hn : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hell j
  unfold Sx
  refine (two_abs_sum_le _ _ _ (fun μ z => (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
      α * (((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (z + ell ^ j • eU L μ) - Phm (ell ^ j) φ z‖ ^ 2)
      + (((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c z μ‖ ^ 2) / α else 0)) ?_).trans (le_of_eq ?_)
  · intro μ _ z _
    split_ifs
    · have := amgm (Phm (ell ^ j) φ (z + ell ^ j • eU L μ) - Phm (ell ^ j) φ z) (Fl (ell ^ j) (ell ^ j) c z μ)
        (α * ((ell ^ j : ℕ) : ℝ)⁻¹) (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp
    · simp
  · unfold Gs Fsm
    rw [div_eq_mul_inv]
    refine sum_lin2 _ _ _ _ _ _ _ (fun μ z => ?_)
    beta_reduce
    split_ifs <;> ring

theorem bound_B (t : ℝ) (ht : 0 < t) :
    2 * |Bx ell j Rg φ c| ≤ t * Gb ell j Rg φ + Fbg ell j Rg c / t := by
  classical
  have hN : (0 : ℝ) < ((ell ^ j * ell : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (pow_pos hell j) hell
  unfold Bx
  refine (two_abs_sum_le _ _ _ (fun μ Z => (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
      t * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j * ell) φ (Z + (ell ^ j * ell) • eU L μ)
        - Phm (ell ^ j * ell) φ Z‖ ^ 2)
      + (((ell ^ j * ell : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2) / t else 0)) ?_).trans (le_of_eq ?_)
  · intro μ _ Z _
    split_ifs
    · have := amgm (Phm (ell ^ j * ell) φ (Z + (ell ^ j * ell) • eU L μ) - Phm (ell ^ j * ell) φ Z)
        (Fl (ell ^ j) (ell ^ j * ell) c Z μ) (t * ((ell ^ j * ell : ℕ) : ℝ)⁻¹) (by positivity)
      refine this.trans (le_of_eq ?_)
      field_simp
    · simp
  · unfold Gb Fbg
    rw [div_eq_mul_inv]
    refine sum_lin2 _ _ _ _ _ _ _ (fun μ Z => ?_)
    beta_reduce
    split_ifs <;> ring

theorem bound_D (τ : ℝ) (hτ : 0 < τ) :
    2 * |Dx ell j Rg φ c| ≤ (ell : ℝ) ^ 2 * (τ * DPh ell j Rg φ + FBs ell j Rg c / τ) := by
  classical
  have hN : (0 : ℝ) < ((ell ^ j * ell : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (pow_pos hell j) hell
  have hl2 : (0 : ℝ) ≤ (ell : ℝ) ^ 2 := by positivity
  have key : ∀ (x y : SuTwo), 2 * |(ell : ℝ) ^ 2 * ⟪x, y⟫|
      ≤ (ell : ℝ) ^ 2 * (τ * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖x‖ ^ 2) + (((ell ^ j * ell : ℕ) : ℝ) * ‖y‖ ^ 2) / τ) := by
    intro x y
    have := amgm x y (τ * ((ell ^ j * ell : ℕ) : ℝ)⁻¹) (by positivity)
    rw [abs_mul, abs_of_nonneg hl2]
    have e : τ * ((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖x‖ ^ 2 + ‖y‖ ^ 2 / (τ * ((ell ^ j * ell : ℕ) : ℝ)⁻¹)
        = τ * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖x‖ ^ 2) + (((ell ^ j * ell : ℕ) : ℝ) * ‖y‖ ^ 2) / τ := by
      field_simp
    rw [e] at this
    nlinarith
  unfold Dx
  refine (two_abs_sum_le _ _ _ (fun μ Z => (if Z ∉ Rg then
      ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
        (ell : ℝ) ^ 2 * (τ * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Ptop ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2)
          + (((ell ^ j * ell : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2) / τ) else 0)
      + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
        (ell : ℝ) ^ 2 * (τ * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2)
          + (((ell ^ j * ell : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2) / τ)
        else 0)) else 0)) ?_).trans (le_of_eq ?_)
  · intro μ _ Z _
    refine two_abs_ite _ _ _ (fun _ => ?_)
    exact two_abs_ite_sub _ _ _ _ _ _ (fun _ => key _ _) (fun _ => key _ _)
  · rw [show (ell : ℝ) ^ 2 * (τ * DPh ell j Rg φ + FBs ell j Rg c / τ)
        = ((ell : ℝ) ^ 2 * τ) * DPh ell j Rg φ + FBs ell j Rg c * ((ell : ℝ) ^ 2 / τ) by ring]
    unfold DPh FBs
    refine sum_lin2 _ _ _ _ _ _ _ (fun μ Z => ?_)
    beta_reduce
    split_ifs <;> ring

theorem bound_L (ρ : ℝ) (hρ : 0 < ρ) :
    2 * |Lx ell j Rg φ c| ≤ ρ * LPh ell j Rg φ + LF ell j Rg c / ρ := by
  classical
  have hn : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hell j
  have key : ∀ (μ : Fin 3) (x y : (Fin 3 → ℕ) → SuTwo), 2 * |∑ k ∈ face ell μ, ⟪x k, y k⟫|
      ≤ ∑ k ∈ face ell μ, (ρ * (((ell ^ j : ℕ) : ℝ)⁻¹ * ‖x k‖ ^ 2) + (((ell ^ j : ℕ) : ℝ) * ‖y k‖ ^ 2) / ρ) := by
    intro μ x y
    refine (two_abs_inner_sum (face ell μ) x y (ρ * ((ell ^ j : ℕ) : ℝ)⁻¹) (by positivity)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    field_simp
  unfold Lx
  refine (two_abs_sum_le _ _ _ (fun μ Z => (if Z ∉ Rg then
      ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
        (ρ * (((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ) - Phm (ell ^ j * ell) φ Z‖ ^ 2)
          + (((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2) / ρ) else 0)
      + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
        (ρ * (((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z‖ ^ 2)
          + (((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2) / ρ) else 0)) else 0)) ?_).trans
    (le_of_eq ?_)
  · intro μ _ Z _
    refine two_abs_ite _ _ _ (fun _ => ?_)
    exact two_abs_ite_sub _ _ _ _ _ _ (fun _ => key μ _ _) (fun _ => key μ _ _)
  · rw [div_eq_mul_inv]
    unfold LPh LF
    refine sum_lin2 _ _ _ _ _ _ _ (fun μ Z => ?_)
    beta_reduce
    split_ifs <;> (try simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]) <;> ring

#print axioms two_abs_sum_le
#print axioms dev_avg
#print axioms onLat_mul_smul
#print axioms two_abs_ite
#print axioms two_abs_ite_sub
#print axioms sum_lin2
#print axioms two_abs_inner_sum
#print axioms bound_S
#print axioms bound_B
#print axioms bound_D
#print axioms bound_L

end amgm_bounds

end AdalyFormal.LemIFlat
