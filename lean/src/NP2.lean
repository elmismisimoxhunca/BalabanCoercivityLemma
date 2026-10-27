import NP1

/-!
# NP2 -- the decay estimates (DE2 `S_bound`, DE3 `interior_bound`) at a GENERAL configuration (m1_patch_nonflat, 2026-10-14)

The flat proofs used `Δh` CONSTANT on each class (pointwise) only through two consequences, which are stated here as
hypotheses, per class `C` lying inside `K` (`k = Δ_U h`, `h = Δ_U μ`):
* `hperp` : `Σ_{z ∈ C} ⟪k z, μ z⟫ = 0`   (flat: constant `k` against zero class sums; covariant: the row identity);
* `hkC`   : `Σ_{z ∈ C} ‖k z‖² ≤ Kq² · nn⁻⁴ · Σ_{z ∈ C} ‖h z‖²`   (flat: the bump bound; covariant: NP3), used only for `B ≥ 24`.
Poincaré is a hypothesis with a free factor `Pk ≥ 1`: `‖μ‖² ≤ Pk (ell B)² ‖D_U μ‖²`.
* `sum_fiber` : `Σ_x F x = Σ_x nn(x)⁻³ Σ_{z ∈ cls x} F z`;
* `poinc_cons_cov` : `‖D_U μ‖² ≤ P ‖Δ_U μ‖²`, `‖μ‖² ≤ P² ‖Δ_U μ‖²`;
* **`S_bound_cov`** : `Σ g ‖h‖² ≤ CAc ell Pk Kq · (B/R) · ‖h‖²`;
* **`interior_bound_cov`** : `gradOn U (Ball w s) h ≤ CBc Kq / B² · Σ_{Ball w ρY} ‖h‖²`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.M1Decay (mulR mulR_apply lapR normSq_site normSq_bond sum_shift sum_back LipP ramp ramp_lip ramp_nonneg
  ramp_le_one ramp_one ramp_zero bond_ineq inner_bond pdist_back_le Classes norm_mulR_le)
open AdalyFormal.M1W2 (gradOn)

variable {L : PeriodicLatticeExtent}

/-- the constant of `S_bound_cov`. -/
noncomputable def CAc (ell : ℕ) (Pk Kq : ℝ) : ℝ :=
  3 * Kq * Pk * (ell : ℝ) ^ 2 + 19044 * Pk * (ell : ℝ) ^ 3 + 6 * Pk * (ell : ℝ) ^ 2 + 12 * Pk * ell

/-- the constant of `interior_bound_cov`. -/
noncomputable def CBc (Kq : ℝ) : ℝ := 2 * Kq + 12708

theorem poinc_cons_cov (U : Cfg L) (μ : SiteL2 L) (P : ℝ) (hP0 : 0 ≤ P) (hP : ‖μ‖ ^ 2 ≤ P * ‖gradL2 U μ‖ ^ 2) :
    ‖gradL2 U μ‖ ^ 2 ≤ P * ‖lapFull U μ‖ ^ 2 ∧ ‖μ‖ ^ 2 ≤ P ^ 2 * ‖lapFull U μ‖ ^ 2 := by
  set D := ‖gradL2 U μ‖ ^ 2 with hD
  set H := ‖lapFull U μ‖ with hH
  have hD0 : 0 ≤ D := sq_nonneg _
  have h1 : D ≤ ‖μ‖ * H := by
    rw [hD, ← inner_lapFull]; exact real_inner_le_norm _ _
  have h2 : D ^ 2 ≤ P * D * H ^ 2 := by
    have := pow_le_pow_left₀ hD0 h1 2
    calc D ^ 2 ≤ (‖μ‖ * H) ^ 2 := this
      _ = ‖μ‖ ^ 2 * H ^ 2 := by ring
      _ ≤ (P * D) * H ^ 2 := mul_le_mul_of_nonneg_right hP (sq_nonneg _)
  have h3 : D ≤ P * H ^ 2 := by
    rcases hD0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : D * D ≤ D * (P * H ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
  refine ⟨h3, ?_⟩
  calc ‖μ‖ ^ 2 ≤ P * D := hP
    _ ≤ P * (P * H ^ 2) := mul_le_mul_of_nonneg_left h3 hP0
    _ = P ^ 2 * H ^ 2 := by ring

namespace ClassesC
variable {B ell : ℕ} (Cl : Classes L B ell)

theorem nn_pos (hB : 1 ≤ B) (x : PeriodicLatticeSite L) : (0 : ℝ) < Cl.nn x := by
  have : (B : ℝ) ≤ Cl.nn x := by exact_mod_cast Cl.nn_ge x
  have : (1 : ℝ) ≤ B := by exact_mod_cast hB
  linarith

/-- every sum is the sum of its class averages times the class size. -/
theorem sum_fiber (hB : 1 ≤ B) (F : PeriodicLatticeSite L → ℝ) :
    ∑ x, F x = ∑ x, ((Cl.nn x : ℝ) ^ 3)⁻¹ * ∑ z ∈ Cl.cls x, F z := by
  rw [Cl.sum_cls_const (fun n => ((n : ℝ) ^ 3)⁻¹) F]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  have := nn_pos Cl hB z
  field_simp

/-- the class-constant part pairs to zero (row-identity form). -/
theorem sum_anc_zero_cov (hB : 1 ≤ B) (μ k : SiteL2 L) (γ : PeriodicLatticeSite L → ℝ)
    (hperp : ∀ x, γ (Cl.anc x) ≠ 0 → ∑ z ∈ Cl.cls x, ⟪k z, μ z⟫ = 0) :
    ∑ x, ⟪k x, γ (Cl.anc x) • μ x⟫ = 0 := by
  rw [sum_fiber Cl hB]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  by_cases hg : γ (Cl.anc x) = 0
  · rw [Finset.sum_eq_zero (fun z hz => by rw [(Cl.mem_cls x z).mp hz, hg, zero_smul, inner_zero_right]), mul_zero]
  · rw [Finset.sum_congr rfl (fun z hz => by rw [(Cl.mem_cls x z).mp hz, real_inner_smul_right]), ← Finset.mul_sum,
      hperp x hg, mul_zero, mul_zero]

open Classical in
/-- **`S_bound` at a general configuration**. -/
theorem S_bound_cov (U : Cfg L) (hell : 2 ≤ ell) (hB : 1 ≤ B) (μ : SiteL2 L) (Pk Kq : ℝ) (hPk : 1 ≤ Pk)
    (hKq : 0 ≤ Kq)
    (hP : ‖μ‖ ^ 2 ≤ Pk * ((ell : ℝ) * B) ^ 2 * ‖gradL2 U μ‖ ^ 2)
    (K : Set (PeriodicLatticeSite L))
    (hperp : ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) →
      ∑ z ∈ Cl.cls x, ⟪lapFull U (lapFull U μ) z, μ z⟫ = 0)
    (hkC : 24 ≤ B → ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) →
      ∑ z ∈ Cl.cls x, ‖lapFull U (lapFull U μ) z‖ ^ 2
        ≤ Kq ^ 2 * ((Cl.nn x : ℝ) ^ 4)⁻¹ * ∑ z ∈ Cl.cls x, ‖lapFull U μ z‖ ^ 2)
    (g : PeriodicLatticeSite L → ℝ) (R : ℕ) (hR : 0 < R) (hRB : B ≤ R)
    (hg0 : ∀ x, 0 ≤ g x) (hglip : LipP g (1 / R)) (hglap : ∀ x, |lapR g x| ≤ 6 / ((R : ℝ) * R))
    (hgK : ∀ x, g x ≠ 0 → ∀ z ∈ Cl.cls x, z ∈ K) :
    ∑ x, g x * ‖lapFull U μ x‖ ^ 2 ≤ CAc ell Pk Kq * ((B : ℝ) / R) * ‖lapFull U μ‖ ^ 2 := by
  set h := lapFull U μ with hh
  set k := lapFull U h with hk
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hell' : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hBR : (B : ℝ) / R ≤ 1 := by rw [div_le_one hR']; exact_mod_cast hRB
  have hBR0 : 0 ≤ (B : ℝ) / R := by positivity
  set P : ℝ := Pk * ((ell : ℝ) * B) ^ 2 with hPdef
  have hP0 : 0 ≤ P := by positivity
  obtain ⟨hDμ, hμ⟩ := poinc_cons_cov U μ P hP0 hP
  have hH0 : 0 ≤ ‖h‖ := norm_nonneg _
  have hμ' : ‖μ‖ ≤ P * ‖h‖ := by
    have : ‖μ‖ ^ 2 ≤ (P * ‖h‖) ^ 2 := by rw [mul_pow]; exact hμ
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp this
  have hgK' : ∀ x, g (Cl.anc x) ≠ 0 → ∀ z ∈ Cl.cls x, z ∈ K := by
    intro x hx z hz
    exact hgK (Cl.anc x) hx z (by rw [AdalyFormal.M1Decay.Classes.cls_anc Cl hB]; exact hz)
  have hosc : ∀ x, |g x - g (Cl.anc x)| ≤ 3 * (Cl.nn x : ℝ) / R := by
    intro x
    have h1 := hglip x (Cl.anc x)
    have h2 : (pdist x (Cl.anc x) : ℝ) ≤ 3 * (Cl.nn x : ℝ) := by exact_mod_cast Cl.pdist_self_anc x
    calc |g x - g (Cl.anc x)| ≤ 1 / R * (pdist x (Cl.anc x) : ℝ) := h1
      _ ≤ 1 / R * (3 * (Cl.nn x : ℝ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * (Cl.nn x : ℝ) / R := by ring
  have hnnle : ∀ x, (Cl.nn x : ℝ) ≤ ell * B := fun x => by exact_mod_cast Cl.nn_le x
  have hnnge : ∀ x, (B : ℝ) ≤ Cl.nn x := fun x => by exact_mod_cast Cl.nn_ge x
  set T1 := ∑ x, ⟪k x, (g x - g (Cl.anc x)) • μ x⟫ with hT1
  have hT1eq : ⟪k, mulR g μ⟫ = T1 := by
    have hz := sum_anc_zero_cov Cl hB μ k g (fun x hx => hperp x (hgK' x hx))
    have e : ⟪k, mulR g μ⟫ = T1 + ∑ x, ⟪k x, g (Cl.anc x) • μ x⟫ := by
      rw [hT1, ← Finset.sum_add_distrib, PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [mulR_apply, sub_smul, inner_sub_right]; ring
    rw [e, hz, add_zero]
  have hT1b : |T1| ≤ (3 * Kq * Pk * (ell : ℝ) ^ 2 + 19044 * Pk * (ell : ℝ) ^ 3) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
    by_cases hB24 : 24 ≤ B
    · set A : PeriodicLatticeSite L → ℝ := fun x =>
        if (∀ z ∈ Cl.cls x, z ∈ K) then ‖k x‖ * Cl.nn x else 0 with hA
      set b : PeriodicLatticeSite L → ℝ := fun x => 3 / (R : ℝ) * ‖μ x‖ with hb
      have hterm : ∀ x, |⟪k x, (g x - g (Cl.anc x)) • μ x⟫| ≤ A x * b x := by
        intro x
        by_cases hin : ∀ z ∈ Cl.cls x, z ∈ K
        · have hAx : A x = ‖k x‖ * Cl.nn x := if_pos hin
          rw [hAx]
          calc |⟪k x, (g x - g (Cl.anc x)) • μ x⟫| ≤ ‖k x‖ * ‖(g x - g (Cl.anc x)) • μ x‖ :=
                abs_real_inner_le_norm _ _
            _ = ‖k x‖ * (|g x - g (Cl.anc x)| * ‖μ x‖) := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ‖k x‖ * (3 * (Cl.nn x : ℝ) / R * ‖μ x‖) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hosc x) (norm_nonneg _)) (norm_nonneg _)
            _ = ‖k x‖ * Cl.nn x * (3 / (R : ℝ) * ‖μ x‖) := by ring
        · have g1 : g x = 0 := by by_contra hne; exact hin (hgK x hne)
          have g2 : g (Cl.anc x) = 0 := by by_contra hne; exact hin (hgK' x hne)
          rw [g1, g2, sub_self, zero_smul, inner_zero_right, abs_zero]
          have hAx : A x = 0 := if_neg hin
          rw [hAx, zero_mul]
      -- class sums of A²
      have hAcls : ∀ x, ∑ z ∈ Cl.cls x, A z ^ 2
          ≤ Kq ^ 2 * ((Cl.nn x : ℝ) ^ 2)⁻¹ * ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 := by
        intro x
        have hnpos := nn_pos Cl hB x
        by_cases hin : ∀ z ∈ Cl.cls x, z ∈ K
        · have e : ∀ z ∈ Cl.cls x, A z ^ 2 = (Cl.nn x : ℝ) ^ 2 * ‖k z‖ ^ 2 := by
            intro z hz
            have hcz : Cl.cls z = Cl.cls x := by
              ext u; rw [Cl.mem_cls, Cl.mem_cls, (Cl.mem_cls x z).mp hz]
            have hinz : ∀ u ∈ Cl.cls z, u ∈ K := by rw [hcz]; exact hin
            have hAz : A z = ‖k z‖ * Cl.nn z := if_pos hinz
            rw [hAz, Cl.nn_cls x z hz]; ring
          rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
          have hk2 := hkC hB24 x hin
          calc (Cl.nn x : ℝ) ^ 2 * ∑ z ∈ Cl.cls x, ‖k z‖ ^ 2
              ≤ (Cl.nn x : ℝ) ^ 2 * (Kq ^ 2 * ((Cl.nn x : ℝ) ^ 4)⁻¹ * ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hk2 (by positivity)
            _ = Kq ^ 2 * ((Cl.nn x : ℝ) ^ 2)⁻¹ * ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 := by field_simp
        · have e : ∀ z ∈ Cl.cls x, A z ^ 2 = 0 := by
            intro z hz
            have hcz : Cl.cls z = Cl.cls x := by
              ext u; rw [Cl.mem_cls, Cl.mem_cls, (Cl.mem_cls x z).mp hz]
            have hinz : ¬ ∀ u ∈ Cl.cls z, u ∈ K := by rw [hcz]; exact hin
            have hAz : A z = 0 := if_neg hinz
            rw [hAz]; ring
          rw [Finset.sum_congr rfl e, Finset.sum_const_zero]
          have : 0 ≤ ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          positivity
      have hsumA : ∑ x, A x ^ 2 ≤ Kq ^ 2 * ((B : ℝ) ^ 2)⁻¹ * ‖h‖ ^ 2 := by
        calc ∑ x, A x ^ 2 = ∑ x, ((Cl.nn x : ℝ) ^ 3)⁻¹ * ∑ z ∈ Cl.cls x, A z ^ 2 := sum_fiber Cl hB _
          _ ≤ ∑ x, ((Cl.nn x : ℝ) ^ 3)⁻¹ * (Kq ^ 2 * ((Cl.nn x : ℝ) ^ 2)⁻¹ * ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2) :=
              Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hAcls x)
                (by have := nn_pos Cl hB x; positivity))
          _ = ∑ x, Kq ^ 2 * ((Cl.nn x : ℝ) ^ 5)⁻¹ * ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun x _ => ?_)
              have := nn_pos Cl hB x
              field_simp
          _ = ∑ z, ‖h z‖ ^ 2 * (Kq ^ 2 * ((Cl.nn z : ℝ) ^ 5)⁻¹ * (Cl.nn z : ℝ) ^ 3) :=
              Cl.sum_cls_const (fun n => Kq ^ 2 * ((n : ℝ) ^ 5)⁻¹) (fun z => ‖h z‖ ^ 2)
          _ ≤ ∑ z, ‖h z‖ ^ 2 * (Kq ^ 2 * ((B : ℝ) ^ 2)⁻¹) := by
              refine Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
              have hn := hnnge z
              have hnpos : (0 : ℝ) < Cl.nn z := by linarith
              have e : Kq ^ 2 * ((Cl.nn z : ℝ) ^ 5)⁻¹ * (Cl.nn z : ℝ) ^ 3 = Kq ^ 2 * ((Cl.nn z : ℝ) ^ 2)⁻¹ := by
                field_simp
              rw [e]
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
              exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hn 2)
          _ = Kq ^ 2 * ((B : ℝ) ^ 2)⁻¹ * ‖h‖ ^ 2 := by
              rw [normSq_site, Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
      have hsumb : ∑ x, b x ^ 2 = 9 / ((R : ℝ) ^ 2) * ‖μ‖ ^ 2 := by
        rw [normSq_site, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hb]; ring
      have hAb0 : 0 ≤ ∑ x, A x * b x := Finset.sum_nonneg (fun x _ => (abs_nonneg _).trans (hterm x))
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ A b
      have habs : |T1| ≤ ∑ x, A x * b x :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => hterm x))
      have hsq : (∑ x, A x * b x) ^ 2 ≤ (3 * Kq * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2) ^ 2 := by
        have hb2 : ∑ x, b x ^ 2 ≤ 9 / ((R : ℝ) ^ 2) * (P ^ 2 * ‖h‖ ^ 2) := by
          rw [hsumb]; exact mul_le_mul_of_nonneg_left hμ (by positivity)
        calc (∑ x, A x * b x) ^ 2 ≤ (∑ x, A x ^ 2) * ∑ x, b x ^ 2 := hCS
          _ ≤ (Kq ^ 2 * ((B : ℝ) ^ 2)⁻¹ * ‖h‖ ^ 2) * (9 / ((R : ℝ) ^ 2) * (P ^ 2 * ‖h‖ ^ 2)) :=
              mul_le_mul hsumA hb2 (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
                (mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (sq_nonneg _))
          _ = (3 * Kq * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2) ^ 2 := by
              rw [hPdef]
              have hB0 : (B : ℝ) ≠ 0 := by linarith
              field_simp; ring
      have hR0 : 0 ≤ 3 * Kq * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        have : 0 ≤ Pk := by linarith
        positivity
      have hle : ∑ x, A x * b x ≤ 3 * Kq * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 :=
        (pow_le_pow_iff_left₀ hAb0 hR0 (by norm_num)).mp hsq
      have h3 : 0 ≤ 19044 * Pk * (ell : ℝ) ^ 3 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        have : 0 ≤ Pk := by linarith
        positivity
      nlinarith
    · have hB23 : (B : ℝ) ≤ 23 := by
        have : B ≤ 23 := by omega
        exact_mod_cast this
      set F : SiteL2 L := mulR (fun x => g x - g (Cl.anc x)) μ with hF
      have hT1F : T1 = ⟪h, lapFull U F⟫ := by
        rw [← lapFull_symm, PiLp.inner_apply]; rfl
      have hF' : ‖F‖ ≤ 3 * ((ell : ℝ) * B) / R * ‖μ‖ := by
        refine norm_mulR_le _ μ _ (by positivity) (fun x => (hosc x).trans ?_)
        have := hnnle x
        have h3 : 3 * (Cl.nn x : ℝ) ≤ 3 * ((ell : ℝ) * B) := by linarith
        exact div_le_div_of_nonneg_right h3 hR'.le
      have h1 : |T1| ≤ ‖h‖ * (12 * ‖F‖) := by
        rw [hT1F]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (lap_norm_le_cov U F) hH0)
      have h2 : ‖h‖ * (12 * ‖F‖) ≤ ‖h‖ * (12 * (3 * ((ell : ℝ) * B) / R * (P * ‖h‖))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hF'.trans ?_) (by norm_num)) hH0
        exact mul_le_mul_of_nonneg_left hμ' (by positivity)
      have e : ‖h‖ * (12 * (3 * ((ell : ℝ) * B) / R * (P * ‖h‖)))
          = 36 * Pk * (ell : ℝ) ^ 3 * (B : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        rw [hPdef]; field_simp; ring
      have h4 : 36 * Pk * (ell : ℝ) ^ 3 * (B : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2
          ≤ 19044 * Pk * (ell : ℝ) ^ 3 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        have hB2 : (B : ℝ) ^ 2 ≤ 529 := by nlinarith
        have : 0 ≤ Pk * (ell : ℝ) ^ 3 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
          have : 0 ≤ Pk := by linarith
          positivity
        nlinarith
      have h5 : 0 ≤ 3 * Kq * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        have : 0 ≤ Pk := by linarith
        positivity
      nlinarith
  -- the commutator term
  set comm := lapFull U (mulR g μ) - mulR g h with hcomm
  have hcb := comm_bound_cov U g μ (6 / ((R : ℝ) * R)) (1 / R) (by positivity) (by positivity) hglap
    (fun x ν => by
      have := hglip x (periodicLatticeShift x ν)
      have hp : (pdist x (periodicLatticeShift x ν) : ℝ) ≤ 1 := by exact_mod_cast pdist_shift_le x ν
      calc |g x - g (periodicLatticeShift x ν)| ≤ 1 / R * (pdist x (periodicLatticeShift x ν) : ℝ) := this
        _ ≤ 1 / R * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = 1 / R := by ring)
    (fun x ν => by
      have := hglip x (periodicLatticeShiftBack x ν)
      have hp : (pdist x (periodicLatticeShiftBack x ν) : ℝ) ≤ 1 := by exact_mod_cast pdist_back_le x ν
      calc |g x - g (periodicLatticeShiftBack x ν)| ≤ 1 / R * (pdist x (periodicLatticeShiftBack x ν) : ℝ) := this
        _ ≤ 1 / R * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = 1 / R := by ring)
  have hsq12 : Real.sqrt 12 * ‖gradL2 U μ‖ ≤ 12 * Pk * ((ell : ℝ) * B) * ‖h‖ := by
    have hPk0 : 0 ≤ Pk := by linarith
    have : (Real.sqrt 12 * ‖gradL2 U μ‖) ^ 2 ≤ (12 * Pk * ((ell : ℝ) * B) * ‖h‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      have h1 := mul_le_mul_of_nonneg_left hDμ (by norm_num : (0 : ℝ) ≤ 12)
      rw [hPdef] at h1
      have h2 : 12 * (Pk * ((ell : ℝ) * B) ^ 2 * ‖h‖ ^ 2) ≤ (12 * Pk * ((ell : ℝ) * B) * ‖h‖) ^ 2 := by
        have : 12 * Pk ≤ 144 * Pk ^ 2 := by nlinarith
        have h0 : 0 ≤ ((ell : ℝ) * B * ‖h‖) ^ 2 := sq_nonneg _
        nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
  have hcomm_b : |⟪h, comm⟫| ≤ (6 * Pk * (ell : ℝ) ^ 2 + 12 * Pk * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
    have h1 : |⟪h, comm⟫| ≤ ‖h‖ * (6 / ((R : ℝ) * R) * ‖μ‖ + Real.sqrt 12 * (1 / R) * ‖gradL2 U μ‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hcb hH0)
    have h2 : 6 / ((R : ℝ) * R) * ‖μ‖ ≤ 6 / ((R : ℝ) * R) * (P * ‖h‖) :=
      mul_le_mul_of_nonneg_left hμ' (by positivity)
    have h3 : Real.sqrt 12 * (1 / R) * ‖gradL2 U μ‖ ≤ 1 / R * (12 * Pk * ((ell : ℝ) * B) * ‖h‖) := by
      have := mul_le_mul_of_nonneg_left hsq12 (by positivity : (0 : ℝ) ≤ 1 / R)
      linarith
    have e1 : ‖h‖ * (6 / ((R : ℝ) * R) * (P * ‖h‖) + 1 / R * (12 * Pk * ((ell : ℝ) * B) * ‖h‖))
        = (6 * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) + 12 * Pk * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
      rw [hPdef]; field_simp
    have h4 : (6 * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) + 12 * Pk * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2
        ≤ (6 * Pk * (ell : ℝ) ^ 2 + 12 * Pk * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
      have hPk0 : 0 ≤ Pk := by linarith
      have : 6 * Pk * (ell : ℝ) ^ 2 * ((B : ℝ) / R) ≤ 6 * Pk * (ell : ℝ) ^ 2 :=
        mul_le_of_le_one_right (by positivity) hBR
      have h0 : 0 ≤ ((B : ℝ) / R) * ‖h‖ ^ 2 := by positivity
      nlinarith
    calc |⟪h, comm⟫| ≤ _ := h1
      _ ≤ ‖h‖ * (6 / ((R : ℝ) * R) * (P * ‖h‖) + 1 / R * (12 * Pk * ((ell : ℝ) * B) * ‖h‖)) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 h3) hH0
      _ = _ := e1
      _ ≤ _ := h4
  have hS : ∑ x, g x * ‖h x‖ ^ 2 = T1 - ⟪h, comm⟫ := by
    have e1 : ∑ x, g x * ‖h x‖ ^ 2 = ⟪h, mulR g h⟫ := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [mulR_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have e2 : mulR g h = lapFull U (mulR g μ) - comm := by rw [hcomm]; abel
    rw [e1, e2, inner_sub_right, ← lapFull_symm U h (mulR g μ), ← hk, hT1eq]
  rw [hS]
  unfold CAc
  have := abs_le.mp hT1b
  have := abs_le.mp hcomm_b
  nlinarith

open Classical in
/-- **`interior_bound` at a general configuration**. -/
theorem interior_bound_cov (U : Cfg L) (hell : 2 ≤ ell) (hB : 1 ≤ B) (μ : SiteL2 L) (Kq : ℝ) (hKq : 0 ≤ Kq)
    (K : Set (PeriodicLatticeSite L))
    (hkC : 24 ≤ B → ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) →
      ∑ z ∈ Cl.cls x, ‖lapFull U (lapFull U μ) z‖ ^ 2
        ≤ Kq ^ 2 * ((Cl.nn x : ℝ) ^ 4)⁻¹ * ∑ z ∈ Cl.cls x, ‖lapFull U μ z‖ ^ 2)
    (w : PeriodicLatticeSite L) (s ρY : ℕ) (hρY : s + 2 + B + 6 * (ell * B) ≤ ρY)
    (hKY : ∀ x, pdist w x ≤ s + 1 + B → ∀ z ∈ Cl.cls x, z ∈ K) :
    gradOn U (Ball w s) (lapFull U μ)
      ≤ CBc Kq / (B : ℝ) ^ 2 * ∑ x, (if pdist w x ≤ ρY then ‖lapFull U μ x‖ ^ 2 else 0) := by
  set h := lapFull U μ with hh
  set k := lapFull U h with hk
  set η := ramp w (s + 1) B with hη
  set hY : SiteL2 L := WithLp.toLp 2 (fun z => if pdist w z ≤ ρY then h z else 0) with hhY
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hYn : ‖hY‖ ^ 2 = ∑ x, (if pdist w x ≤ ρY then ‖h x‖ ^ 2 else 0) := by
    rw [normSq_site]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show ‖(if pdist w x ≤ ρY then h x else 0)‖ ^ 2 = _
    split_ifs <;> simp
  rw [← hYn]
  have hηlip := ramp_lip w (s + 1) B hB
  have hη0 : ∀ x, 0 ≤ η x := ramp_nonneg w (s + 1) B
  have hη1 : ∀ x, η x ≤ 1 := ramp_le_one w (s + 1) B
  have hηone : ∀ x, pdist w x ≤ s + 1 → η x = 1 := fun x hx => ramp_one w (s + 1) B hB x hx
  have hηzero : ∀ x, s + 1 + B ≤ pdist w x → η x = 0 := fun x hx => ramp_zero w (s + 1) B hB x hx
  have hηY : ∀ x, η x ≠ 0 → pdist w x ≤ s + 1 + B := by
    intro x hx; by_contra hc; exact hx (hηzero x (by omega))
  have hYeq : ∀ x, pdist w x ≤ ρY → hY x = h x := fun x hx => by
    show (if pdist w x ≤ ρY then h x else 0) = h x; rw [if_pos hx]
  -- step 1
  set W : PeriodicLatticeSite L → Fin 3 → ℝ := fun x μ =>
    (η x ^ 2 + η (periodicLatticeShift x μ) ^ 2) / 4 *
      ‖RMap (U (x, μ)) (h (periodicLatticeShift x μ)) - h x‖ ^ 2 with hW
  have step1 : gradOn U (Ball w s) h ≤ 2 * ∑ x, ∑ μ : Fin 3, W x μ := by
    unfold gradOn
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun μ _ => ?_)
    have hWnn : 0 ≤ W x μ := by simp only [hW]; positivity
    split_ifs with hb
    · have hs1 := pdist_shift_le x μ
      have hx1 : pdist w x ≤ s + 1 := by
        rcases hb with hb | hb
        · exact le_trans hb (Nat.le_succ s)
        · have := pdist_triangle w (periodicLatticeShift x μ) x
          rw [pdist_comm (periodicLatticeShift x μ) x] at this
          have hb' : pdist w (periodicLatticeShift x μ) ≤ s := hb
          omega
      have hx2 : pdist w (periodicLatticeShift x μ) ≤ s + 1 := by
        rcases hb with hb | hb
        · have := pdist_triangle w x (periodicLatticeShift x μ)
          have hb' : pdist w x ≤ s := hb
          omega
        · exact le_trans hb (Nat.le_succ s)
      simp only [hW]
      rw [hηone x hx1, hηone _ hx2, grad_cov]
      dsimp only
      apply le_of_eq; ring
    · linarith
  -- step 2
  set Fη : SiteL2 L := mulR (fun z => η z ^ 2) h with hFη
  have step2 : ∑ x, ∑ μ : Fin 3, W x μ ≤ ⟪k, Fη⟫ + ∑ x, ∑ μ : Fin 3,
      1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 *
        ‖h x + RMap (U (x, μ)) (h (periodicLatticeShift x μ))‖ ^ 2 := by
    have e : ⟪k, Fη⟫ = ∑ x, ∑ μ : Fin 3, ⟪RMap (U (x, μ)) (h (periodicLatticeShift x μ)) - h x,
        η (periodicLatticeShift x μ) ^ 2 • RMap (U (x, μ)) (h (periodicLatticeShift x μ)) - η x ^ 2 • h x⟫ := by
      rw [hk, ← inner_grad_grad_cov, inner_bond]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun μ _ => ?_))
      rw [grad_cov, grad_cov]
      show ⟪_, RMap (U (x, μ)) (η (periodicLatticeShift x μ) ^ 2 • h (periodicLatticeShift x μ)) - η x ^ 2 • h x⟫ = _
      rw [map_smul]
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun μ _ => ?_)
    exact bond_ineq (h x) (RMap (U (x, μ)) (h (periodicLatticeShift x μ))) (η x) (η (periodicLatticeShift x μ))
  -- step 3
  have step3 : ∑ x, ∑ μ : Fin 3, 1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 *
      ‖h x + RMap (U (x, μ)) (h (periodicLatticeShift x μ))‖ ^ 2 ≤ 6 / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
    have hpt : ∀ x (μ : Fin 3), 1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 *
        ‖h x + RMap (U (x, μ)) (h (periodicLatticeShift x μ))‖ ^ 2
        ≤ 1 / (B : ℝ) ^ 2 * (‖hY x‖ ^ 2 + ‖hY (periodicLatticeShift x μ)‖ ^ 2) := by
      intro x μ
      by_cases heq : η (periodicLatticeShift x μ) = η x
      · rw [heq, sub_self]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul]
        positivity
      · have hs1 := pdist_shift_le x μ
        have hboth : pdist w x ≤ ρY ∧ pdist w (periodicLatticeShift x μ) ≤ ρY := by
          by_cases h0 : η x = 0
          · have h1 : η (periodicLatticeShift x μ) ≠ 0 := by rw [h0] at heq; exact heq
            have h2 := hηY _ h1
            have := pdist_triangle w (periodicLatticeShift x μ) x
            rw [pdist_comm (periodicLatticeShift x μ) x] at this
            constructor <;> omega
          · have h2 := hηY _ h0
            have := pdist_triangle w x (periodicLatticeShift x μ)
            constructor <;> omega
        rw [hYeq x hboth.1, hYeq _ hboth.2]
        have hl : |η (periodicLatticeShift x μ) - η x| ≤ 1 / B := by
          have := hηlip (periodicLatticeShift x μ) x
          rw [pdist_comm] at this
          have hp : (pdist x (periodicLatticeShift x μ) : ℝ) ≤ 1 := by exact_mod_cast hs1
          calc |η (periodicLatticeShift x μ) - η x| ≤ 1 / B * (pdist x (periodicLatticeShift x μ) : ℝ) := this
            _ ≤ 1 / B * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
            _ = 1 / B := by ring
        have hl2 : (η (periodicLatticeShift x μ) - η x) ^ 2 ≤ 1 / (B : ℝ) ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hl 2
          rw [sq_abs, div_pow, one_pow] at this; exact this
        have hab : ‖h x + RMap (U (x, μ)) (h (periodicLatticeShift x μ))‖ ^ 2
            ≤ 2 * (‖h x‖ ^ 2 + ‖h (periodicLatticeShift x μ)‖ ^ 2) := by
          have := norm_add_le (h x) (RMap (U (x, μ)) (h (periodicLatticeShift x μ)))
          rw [norm_RMap'] at this
          nlinarith [norm_nonneg (h x + RMap (U (x, μ)) (h (periodicLatticeShift x μ))), norm_nonneg (h x),
            norm_nonneg (h (periodicLatticeShift x μ)), sq_nonneg (‖h x‖ - ‖h (periodicLatticeShift x μ)‖)]
        calc 1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 *
              ‖h x + RMap (U (x, μ)) (h (periodicLatticeShift x μ))‖ ^ 2
            ≤ 1 / 2 * (1 / (B : ℝ) ^ 2) * (2 * (‖h x‖ ^ 2 + ‖h (periodicLatticeShift x μ)‖ ^ 2)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hl2 (by norm_num)) hab (sq_nonneg _) (by positivity)
          _ = 1 / (B : ℝ) ^ 2 * (‖h x‖ ^ 2 + ‖h (periodicLatticeShift x μ)‖ ^ 2) := by ring
    calc _ ≤ ∑ x, ∑ μ : Fin 3, 1 / (B : ℝ) ^ 2 * (‖hY x‖ ^ 2 + ‖hY (periodicLatticeShift x μ)‖ ^ 2) :=
          Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun μ _ => hpt x μ))
      _ = 1 / (B : ℝ) ^ 2 * ∑ x, ∑ μ : Fin 3, (‖hY x‖ ^ 2 + ‖hY (periodicLatticeShift x μ)‖ ^ 2) := by
          simp only [Finset.mul_sum]
      _ = 6 / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_add_distrib, sum_shift (fun y => ‖hY y‖ ^ 2), Fin.sum_univ_three]
          rw [normSq_site]; ring
  -- step 4
  have step4 : ⟪k, Fη⟫ ≤ (Kq + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
    have hFηY : Fη = mulR (fun z => η z ^ 2) hY := by
      ext1 z
      show η z ^ 2 • h z = η z ^ 2 • (if pdist w z ≤ ρY then h z else 0)
      by_cases hz : η z = 0
      · rw [hz]; simp
      · rw [if_pos (by have := hηY z hz; omega)]
    by_cases hB24 : 24 ≤ B
    · -- the class indicator: the class meets the ramp support
      set I : PeriodicLatticeSite L → Prop := fun x => ∃ z ∈ Cl.cls x, pdist w z ≤ s + 1 + B with hI
      have hIcls : ∀ x, ∀ z ∈ Cl.cls x, (I z ↔ I x) := by
        intro x z hz
        have hcz : Cl.cls z = Cl.cls x := by
          ext u; rw [Cl.mem_cls, Cl.mem_cls, (Cl.mem_cls x z).mp hz]
        simp only [hI, hcz]
      have hIK : ∀ x, I x → ∀ z ∈ Cl.cls x, z ∈ K := by
        rintro x ⟨z0, hz0, hd⟩ z hz
        have hcz : Cl.cls z0 = Cl.cls x := by
          ext u; rw [Cl.mem_cls, Cl.mem_cls, (Cl.mem_cls x z0).mp hz0]
        exact hKY z0 hd z (by rw [hcz]; exact hz)
      set A : PeriodicLatticeSite L → ℝ := fun x => if I x then ‖k x‖ else 0 with hA
      have hterm : ∀ x, ⟪k x, Fη x⟫ ≤ A x * ‖hY x‖ := by
        intro x
        show ⟪k x, η x ^ 2 • h x⟫ ≤ _
        by_cases hx : η x = 0
        · rw [hx]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, inner_zero_right]
          exact mul_nonneg (by simp only [hA]; split_ifs <;> simp) (norm_nonneg _)
        · have hIx : I x := ⟨x, Cl.self_mem x, hηY x hx⟩
          have hAx : A x = ‖k x‖ := if_pos hIx
          rw [hAx, hYeq x (by have := hηY x hx; omega), real_inner_smul_right]
          have h4 : ⟪k x, h x⟫ ≤ ‖k x‖ * ‖h x‖ := real_inner_le_norm _ _
          have h0 : 0 ≤ η x ^ 2 := sq_nonneg _
          have h2 : η x ^ 2 ≤ 1 := by
            have a1 := hη1 x
            have a0 := hη0 x
            calc η x ^ 2 = η x * η x := sq _
              _ ≤ 1 * 1 := mul_le_mul a1 a1 a0 zero_le_one
              _ = 1 := one_mul 1
          have h3 : 0 ≤ ‖k x‖ * ‖h x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
          calc η x ^ 2 * ⟪k x, h x⟫ ≤ η x ^ 2 * (‖k x‖ * ‖h x‖) := mul_le_mul_of_nonneg_left h4 h0
            _ ≤ 1 * (‖k x‖ * ‖h x‖) := mul_le_mul_of_nonneg_right h2 h3
            _ = ‖k x‖ * ‖h x‖ := one_mul _
      have hAcls : ∀ x, ∑ z ∈ Cl.cls x, A z ^ 2
          ≤ Kq ^ 2 * ((Cl.nn x : ℝ) ^ 4)⁻¹ * ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 := by
        intro x
        by_cases hIx : I x
        · have e : ∀ z ∈ Cl.cls x, A z ^ 2 = ‖k z‖ ^ 2 := by
            intro z hz
            have hAz : A z = ‖k z‖ := if_pos ((hIcls x z hz).mpr hIx)
            rw [hAz]
          rw [Finset.sum_congr rfl e]
          have hk2 := hkC hB24 x (hIK x hIx)
          have hsY : ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 = ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 := by
            obtain ⟨z0, hz0, hd⟩ := hIx
            have hcz0 : Cl.cls z0 = Cl.cls x := by
              ext u; rw [Cl.mem_cls, Cl.mem_cls, (Cl.mem_cls x z0).mp hz0]
            refine Finset.sum_congr rfl (fun z hz => ?_)
            have hzz0 : z ∈ Cl.cls z0 := by rw [hcz0]; exact hz
            have h1 := Cl.pdist_in_cls z0 z hzz0
            have h3 := pdist_triangle w z0 z
            have h4 := Cl.nn_le z0
            rw [hYeq z (by
              have : 6 * Cl.nn z0 ≤ 6 * (ell * B) := by omega
              omega)]
          rw [← hsY]; exact hk2
        · have e : ∀ z ∈ Cl.cls x, A z ^ 2 = 0 := by
            intro z hz
            have hAz : A z = 0 := if_neg (fun hIz => hIx ((hIcls x z hz).mp hIz))
            rw [hAz]; ring
          rw [Finset.sum_congr rfl e, Finset.sum_const_zero]
          have : 0 ≤ ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          have := nn_pos Cl hB x
          positivity
      have hsumA : ∑ x, A x ^ 2 ≤ Kq ^ 2 * ((B : ℝ) ^ 4)⁻¹ * ‖hY‖ ^ 2 := by
        calc ∑ x, A x ^ 2 = ∑ x, ((Cl.nn x : ℝ) ^ 3)⁻¹ * ∑ z ∈ Cl.cls x, A z ^ 2 := sum_fiber Cl hB _
          _ ≤ ∑ x, ((Cl.nn x : ℝ) ^ 3)⁻¹ * (Kq ^ 2 * ((Cl.nn x : ℝ) ^ 4)⁻¹ * ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2) :=
              Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hAcls x)
                (by have := nn_pos Cl hB x; positivity))
          _ = ∑ x, Kq ^ 2 * ((Cl.nn x : ℝ) ^ 7)⁻¹ * ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun x _ => ?_)
              have := nn_pos Cl hB x
              field_simp
          _ = ∑ z, ‖hY z‖ ^ 2 * (Kq ^ 2 * ((Cl.nn z : ℝ) ^ 7)⁻¹ * (Cl.nn z : ℝ) ^ 3) :=
              Cl.sum_cls_const (fun n => Kq ^ 2 * ((n : ℝ) ^ 7)⁻¹) (fun z => ‖hY z‖ ^ 2)
          _ ≤ ∑ z, ‖hY z‖ ^ 2 * (Kq ^ 2 * ((B : ℝ) ^ 4)⁻¹) := by
              refine Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
              have hn : (B : ℝ) ≤ Cl.nn z := by exact_mod_cast Cl.nn_ge z
              have hnpos : (0 : ℝ) < Cl.nn z := by linarith
              have e : Kq ^ 2 * ((Cl.nn z : ℝ) ^ 7)⁻¹ * (Cl.nn z : ℝ) ^ 3 = Kq ^ 2 * ((Cl.nn z : ℝ) ^ 4)⁻¹ := by
                field_simp
              rw [e]
              exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hn 4))
                (sq_nonneg _)
          _ = Kq ^ 2 * ((B : ℝ) ^ 4)⁻¹ * ‖hY‖ ^ 2 := by
              rw [normSq_site, Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ A (fun x => ‖hY x‖)
      have hA0 : 0 ≤ ∑ x, A x * ‖hY x‖ := by
        refine Finset.sum_nonneg (fun x _ => mul_nonneg ?_ (norm_nonneg _))
        simp only [hA]; split_ifs <;> simp
      have hsq : (∑ x, A x * ‖hY x‖) ^ 2 ≤ (Kq / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) ^ 2 := by
        calc (∑ x, A x * ‖hY x‖) ^ 2 ≤ (∑ x, A x ^ 2) * ∑ x, ‖hY x‖ ^ 2 := hCS
          _ ≤ (Kq ^ 2 * ((B : ℝ) ^ 4)⁻¹ * ‖hY‖ ^ 2) * ‖hY‖ ^ 2 := by
              rw [← normSq_site]
              exact mul_le_mul_of_nonneg_right hsumA (sq_nonneg _)
          _ = (Kq / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) ^ 2 := by field_simp
      have hRHS0 : 0 ≤ Kq / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 :=
        mul_nonneg (div_nonneg hKq (by positivity)) (sq_nonneg _)
      have hle := (pow_le_pow_iff_left₀ hA0 hRHS0 (by norm_num)).mp hsq
      have hsplit : ⟪k, Fη⟫ ≤ ∑ x, A x * ‖hY x‖ := by
        rw [PiLp.inner_apply]; exact Finset.sum_le_sum (fun x _ => hterm x)
      have : Kq / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 ≤ (Kq + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    · have hB23 : (B : ℝ) ≤ 23 := by
        have : B ≤ 23 := by omega
        exact_mod_cast this
      have hsupp : ∀ z, s + 1 + B ≤ pdist w z → Fη z = 0 := by
        intro z hz
        show η z ^ 2 • h z = 0
        rw [hηzero z hz]; simp
      have hlapY : ⟪h, lapFull U Fη⟫ = ⟪hY, lapFull U Fη⟫ := by
        rw [PiLp.inner_apply, PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : pdist w x ≤ ρY
        · rw [hYeq x hx]
        · rw [lap_zero_far_cov U Fη w (s + 1 + B) hsupp x (by omega)]
          simp
      have h1 : ⟪k, Fη⟫ = ⟪hY, lapFull U Fη⟫ := by rw [hk, lapFull_symm, hlapY]
      have h2 : ‖Fη‖ ≤ ‖hY‖ := by
        rw [hFηY]
        have := norm_mulR_le (fun z => η z ^ 2) hY 1 (by norm_num) (fun z => by
          rw [abs_of_nonneg (sq_nonneg _)]; have := hη1 z; have := hη0 z; nlinarith)
        linarith
      have h3 : ⟪k, Fη⟫ ≤ 12 * ‖hY‖ ^ 2 := by
        rw [h1]
        calc ⟪hY, lapFull U Fη⟫ ≤ ‖hY‖ * ‖lapFull U Fη‖ := real_inner_le_norm _ _
          _ ≤ ‖hY‖ * (12 * ‖Fη‖) := mul_le_mul_of_nonneg_left (lap_norm_le_cov U Fη) (norm_nonneg _)
          _ ≤ ‖hY‖ * (12 * ‖hY‖) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ = 12 * ‖hY‖ ^ 2 := by ring
      have h4 : 12 ≤ (Kq + 6348) / (B : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have hBB := mul_le_mul hB23 hB23 (by positivity) (by norm_num)
        nlinarith
      calc ⟪k, Fη⟫ ≤ 12 * ‖hY‖ ^ 2 := h3
        _ ≤ (Kq + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  unfold CBc
  have e : (2 * Kq + 12708) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2
      = 2 * ((Kq + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) + 2 * (6 / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) := by ring
  rw [e]
  linarith

end ClassesC

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.poinc_cons_cov
#print axioms AdalyFormal.M1NonFlat.ClassesC.sum_fiber
#print axioms AdalyFormal.M1NonFlat.ClassesC.sum_anc_zero_cov
#print axioms AdalyFormal.M1NonFlat.ClassesC.S_bound_cov
#print axioms AdalyFormal.M1NonFlat.ClassesC.interior_bound_cov
