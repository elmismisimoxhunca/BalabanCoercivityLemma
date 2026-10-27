import DE1

/-!
# DE2 -- the second-order Caccioppoli estimate with a smooth cutoff (m1_w2_decay, 2026-10-13)

Setting: `μ` with zero class sums, Poincaré `‖μ‖² ≤ 6(ℓB)²‖Dμ‖²`, `h = Δμ`, `Δh` constant on every class inside `K`;
`g ≥ 0` with `LipP g (1/R)`, `|lapR g| ≤ 6/R²`, `B ≤ R`, and every class meeting `supp g` inside `K`.
**`S_bound`** : `Σ_x g x ‖h x‖² ≤ CA ℓ · (B/R) · ‖h‖²`, `CA ℓ = 18 Kb ℓ² + 114264 ℓ³ + 36 ℓ² + 9 ℓ`, `Kb = 6·48²·72³`.
Proof: `Σ g|h|² = ⟪Δh, g μ⟫ − ⟪h, [Δ,g]μ⟫`; `⟪Δh, gμ⟫ = Σ_x ⟪Δh x, (g x − g(anc x)) μ x⟫` (zero class sums); for `B ≥ 24`
each `|Δh x|` is bounded by the bump estimate on its class, for `B < 24` by `‖Δ‖ ≤ 12`; the commutator by `comm_bound`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1Decay

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

/-- `Kb = 6·48²·72³`, `Kb² = Kb2`. -/
noncomputable def Kb : ℝ := 6 * 48 ^ 2 * 72 ^ 3

theorem Kb2_eq : Kb2 = Kb ^ 2 := by unfold Kb2 Kb; norm_num

theorem Kb_pos : 0 < Kb := by unfold Kb; norm_num

/-- the constant of `S_bound`. -/
noncomputable def CA (ell : ℕ) : ℝ := 18 * Kb * (ell : ℝ) ^ 2 + 114264 * (ell : ℝ) ^ 3 + 36 * (ell : ℝ) ^ 2 + 9 * ell

theorem norm_mulR_le (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) (M : ℝ) (hM : 0 ≤ M) (h : ∀ x, |φ x| ≤ M) :
    ‖mulR φ f‖ ≤ M * ‖f‖ := by
  have h1 : ‖mulR φ f‖ ^ 2 ≤ (M * ‖f‖) ^ 2 := by
    rw [normSq_site, mul_pow, normSq_site, Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [mulR_apply, norm_smul, mul_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (h x) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h1

theorem poinc_cons (μ : SiteL2 L) (P : ℝ) (hP0 : 0 ≤ P) (hP : ‖μ‖ ^ 2 ≤ P * ‖gradL2 (U0 L) μ‖ ^ 2) :
    ‖gradL2 (U0 L) μ‖ ^ 2 ≤ P * ‖lapFull (U0 L) μ‖ ^ 2 ∧ ‖μ‖ ^ 2 ≤ P ^ 2 * ‖lapFull (U0 L) μ‖ ^ 2 := by
  set D := ‖gradL2 (U0 L) μ‖ ^ 2 with hD
  set H := ‖lapFull (U0 L) μ‖ with hH
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

namespace Classes
variable {B ell : ℕ} (Cl : Classes L B ell)

theorem anc_mem (hB : 1 ≤ B) (x : PeriodicLatticeSite L) : Cl.anc x ∈ Cl.cls x := by
  rw [Cl.cls_eq_block, mem_blockOf]
  intro μ
  have := Cl.nn_ge x
  exact ⟨le_refl _, by omega⟩

theorem cls_anc (hB : 1 ≤ B) (x : PeriodicLatticeSite L) : Cl.cls (Cl.anc x) = Cl.cls x := by
  have h := (Cl.mem_cls x (Cl.anc x)).mp (Cl.anc_mem hB x)
  ext z
  rw [Cl.mem_cls, Cl.mem_cls, h]

open Classical in
/-- **the main Caccioppoli bound**. -/
theorem S_bound (hell : 2 ≤ ell) (hB : 1 ≤ B) (μ : SiteL2 L)
    (hsum : ∀ x, ∑ z ∈ Cl.cls x, μ z = 0)
    (hP : ‖μ‖ ^ 2 ≤ 6 * ((ell : ℝ) * B) ^ 2 * ‖gradL2 (U0 L) μ‖ ^ 2)
    (K : Set (PeriodicLatticeSite L))
    (hconst : ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) → ∀ z ∈ Cl.cls x,
      lapFull (U0 L) (lapFull (U0 L) μ) z = lapFull (U0 L) (lapFull (U0 L) μ) x)
    (g : PeriodicLatticeSite L → ℝ) (R : ℕ) (hR : 0 < R) (hRB : B ≤ R)
    (hg0 : ∀ x, 0 ≤ g x) (hglip : LipP g (1 / R)) (hglap : ∀ x, |lapR g x| ≤ 6 / ((R : ℝ) * R))
    (hgK : ∀ x, g x ≠ 0 → ∀ z ∈ Cl.cls x, z ∈ K) :
    ∑ x, g x * ‖lapFull (U0 L) μ x‖ ^ 2
      ≤ CA ell * ((B : ℝ) / R) * ‖lapFull (U0 L) μ‖ ^ 2 := by
  set h := lapFull (U0 L) μ with hh
  set k := lapFull (U0 L) h with hk
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hell' : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hBR : (B : ℝ) / R ≤ 1 := by rw [div_le_one hR']; exact_mod_cast hRB
  have hBR0 : 0 ≤ (B : ℝ) / R := by positivity
  set P : ℝ := 6 * ((ell : ℝ) * B) ^ 2 with hPdef
  have hP0 : 0 ≤ P := by positivity
  obtain ⟨hDμ, hμ⟩ := poinc_cons μ P hP0 hP
  have hH0 : 0 ≤ ‖h‖ := norm_nonneg _
  -- ‖μ‖ ≤ P ‖h‖
  have hμ' : ‖μ‖ ≤ P * ‖h‖ := by
    have : ‖μ‖ ^ 2 ≤ (P * ‖h‖) ^ 2 := by rw [mul_pow]; exact hμ
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp this
  -- class support of g ∘ anc
  have hgK' : ∀ x, g (Cl.anc x) ≠ 0 → ∀ z ∈ Cl.cls x, z ∈ K := by
    intro x hx z hz
    exact hgK (Cl.anc x) hx z (by rw [Cl.cls_anc hB]; exact hz)
  -- oscillation of g on a class
  have hosc : ∀ x, |g x - g (Cl.anc x)| ≤ 3 * (Cl.nn x : ℝ) / R := by
    intro x
    have h1 := hglip x (Cl.anc x)
    have h2 : (pdist x (Cl.anc x) : ℝ) ≤ 3 * (Cl.nn x : ℝ) := by exact_mod_cast Cl.pdist_self_anc x
    calc |g x - g (Cl.anc x)| ≤ 1 / R * (pdist x (Cl.anc x) : ℝ) := h1
      _ ≤ 1 / R * (3 * (Cl.nn x : ℝ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * (Cl.nn x : ℝ) / R := by ring
  have hnnle : ∀ x, (Cl.nn x : ℝ) ≤ ell * B := fun x => by exact_mod_cast Cl.nn_le x
  have hnnge : ∀ x, (B : ℝ) ≤ Cl.nn x := fun x => by exact_mod_cast Cl.nn_ge x
  -- the c-term
  set T1 := ∑ x, ⟪k x, (g x - g (Cl.anc x)) • μ x⟫ with hT1
  have hT1eq : ⟪k, mulR g μ⟫ = T1 := by
    have hz := Cl.sum_anc_zero μ k g hsum (fun x hx z hz => hconst x (hgK' x hx) z hz)
    have e : ⟪k, mulR g μ⟫ = T1 + ∑ x, ⟪k x, g (Cl.anc x) • μ x⟫ := by
      rw [hT1, ← Finset.sum_add_distrib, PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [mulR_apply, sub_smul, inner_sub_right]; ring
    rw [e, hz, add_zero]
  have hT1b : |T1| ≤ (18 * Kb * (ell : ℝ) ^ 2 + 114264 * (ell : ℝ) ^ 3) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
    by_cases hB24 : 24 ≤ B
    · -- large blocks: pointwise bump bound
      set A : PeriodicLatticeSite L → ℝ := fun x =>
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
      have hA2 : ∀ x, A x ^ 2 ≤ Kb2 * ((Cl.nn x : ℝ) ^ 5)⁻¹ * ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 := by
        intro x
        by_cases hin : ∀ z ∈ Cl.cls x, z ∈ K
        · have hAx : A x = ‖k x‖ * Cl.nn x := if_pos hin
          rw [hAx]
          have hn24 : 24 ≤ Cl.nn x := le_trans hB24 (Cl.nn_ge x)
          have hbb := bump_bound (Cl.anc x) (Cl.nn x) hn24 (Cl.fit x) h (k x) (by
            intro z hz
            rw [← Cl.cls_eq_block] at hz
            exact hconst x hin z hz)
          rw [← Cl.cls_eq_block] at hbb
          have hnpos : (0 : ℝ) < Cl.nn x := by have := hnnge x; linarith
          have e : (‖k x‖ * Cl.nn x) ^ 2 = ‖k x‖ ^ 2 * (Cl.nn x : ℝ) ^ 7 * ((Cl.nn x : ℝ) ^ 5)⁻¹ := by
            field_simp
          rw [e]
          have hb2 := mul_le_mul_of_nonneg_right hbb (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (Cl.nn x : ℝ) ^ 5))
          exact hb2.trans (le_of_eq (by ring))
        · have hAx : A x = 0 := if_neg hin
          rw [hAx]
          have : 0 ≤ Kb2 := by unfold Kb2; norm_num
          have h0 : 0 ≤ ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          have : (0 : ℝ) ^ 2 = 0 := by norm_num
          rw [this]; positivity
      have hsumA : ∑ x, A x ^ 2 ≤ Kb2 * ((B : ℝ) ^ 2)⁻¹ * ‖h‖ ^ 2 := by
        calc ∑ x, A x ^ 2 ≤ ∑ x, Kb2 * ((Cl.nn x : ℝ) ^ 5)⁻¹ * ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 :=
              Finset.sum_le_sum (fun x _ => hA2 x)
          _ = ∑ z, ‖h z‖ ^ 2 * (Kb2 * ((Cl.nn z : ℝ) ^ 5)⁻¹ * (Cl.nn z : ℝ) ^ 3) :=
              Cl.sum_cls_const (fun n => Kb2 * ((n : ℝ) ^ 5)⁻¹) (fun z => ‖h z‖ ^ 2)
          _ ≤ ∑ z, ‖h z‖ ^ 2 * (Kb2 * ((B : ℝ) ^ 2)⁻¹) := by
              refine Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
              have hn := hnnge z
              have hnpos : (0 : ℝ) < Cl.nn z := by linarith
              have e : Kb2 * ((Cl.nn z : ℝ) ^ 5)⁻¹ * (Cl.nn z : ℝ) ^ 3 = Kb2 * ((Cl.nn z : ℝ) ^ 2)⁻¹ := by
                field_simp
              rw [e]
              have hK0 : 0 ≤ Kb2 := by unfold Kb2; norm_num
              refine mul_le_mul_of_nonneg_left ?_ hK0
              exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hn 2)
          _ = Kb2 * ((B : ℝ) ^ 2)⁻¹ * ‖h‖ ^ 2 := by
              rw [normSq_site, Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
      have hsumb : ∑ x, b x ^ 2 = 9 / ((R : ℝ) ^ 2) * ‖μ‖ ^ 2 := by
        rw [normSq_site, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hb]; ring
      have hAb0 : 0 ≤ ∑ x, A x * b x := Finset.sum_nonneg (fun x _ => (abs_nonneg _).trans (hterm x))
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ A b
      have habs : |T1| ≤ ∑ x, A x * b x :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => hterm x))
      -- (Σ A b)² ≤ (18 Kb ℓ² B/R ‖h‖²)²
      have hsq : (∑ x, A x * b x) ^ 2 ≤ (18 * Kb * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2) ^ 2 := by
        have hb2 : ∑ x, b x ^ 2 ≤ 9 / ((R : ℝ) ^ 2) * (P ^ 2 * ‖h‖ ^ 2) := by
          rw [hsumb]; exact mul_le_mul_of_nonneg_left hμ (by positivity)
        have hA0 : 0 ≤ ∑ x, A x ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        calc (∑ x, A x * b x) ^ 2 ≤ (∑ x, A x ^ 2) * ∑ x, b x ^ 2 := hCS
          _ ≤ (Kb2 * ((B : ℝ) ^ 2)⁻¹ * ‖h‖ ^ 2) * (9 / ((R : ℝ) ^ 2) * (P ^ 2 * ‖h‖ ^ 2)) :=
              mul_le_mul hsumA hb2 (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
                (mul_nonneg (mul_nonneg (by unfold Kb2; norm_num) (by positivity)) (sq_nonneg _))
          _ = (18 * Kb * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2) ^ 2 := by
              rw [Kb2_eq, hPdef]
              have hB0 : (B : ℝ) ≠ 0 := by linarith
              field_simp; ring
      have hR0 : 0 ≤ 18 * Kb * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        have := Kb_pos
        have h1 : 0 ≤ 18 * Kb * (ell : ℝ) ^ 2 := by positivity
        exact mul_nonneg (mul_nonneg h1 hBR0) (sq_nonneg _)
      have hle : ∑ x, A x * b x ≤ 18 * Kb * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 :=
        (pow_le_pow_iff_left₀ hAb0 hR0 (by norm_num)).mp hsq
      have h3 : 0 ≤ 114264 * (ell : ℝ) ^ 3 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by positivity
      nlinarith
    · -- small blocks: global bound with ‖Δ‖ ≤ 12
      have hB23 : (B : ℝ) ≤ 23 := by
        have : B ≤ 23 := by omega
        exact_mod_cast this
      set F : SiteL2 L := mulR (fun x => g x - g (Cl.anc x)) μ with hF
      have hT1F : T1 = ⟪h, lapFull (U0 L) F⟫ := by
        rw [← lapFull_symm, PiLp.inner_apply]; rfl
      have hF' : ‖F‖ ≤ 3 * ((ell : ℝ) * B) / R * ‖μ‖ := by
        refine norm_mulR_le _ μ _ (by positivity) (fun x => (hosc x).trans ?_)
        have := hnnle x
        have h3 : 3 * (Cl.nn x : ℝ) ≤ 3 * ((ell : ℝ) * B) := by linarith
        exact div_le_div_of_nonneg_right h3 hR'.le
      have h1 : |T1| ≤ ‖h‖ * (12 * ‖F‖) := by
        rw [hT1F]
        exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (lap_norm_le F) hH0)
      have h2 : ‖h‖ * (12 * ‖F‖) ≤ ‖h‖ * (12 * (3 * ((ell : ℝ) * B) / R * (P * ‖h‖))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hF'.trans ?_) (by norm_num)) hH0
        exact mul_le_mul_of_nonneg_left hμ' (by positivity)
      have e : ‖h‖ * (12 * (3 * ((ell : ℝ) * B) / R * (P * ‖h‖)))
          = 216 * (ell : ℝ) ^ 3 * (B : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        rw [hPdef]; field_simp; ring
      have h4 : 216 * (ell : ℝ) ^ 3 * (B : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2
          ≤ 114264 * (ell : ℝ) ^ 3 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        have hB2 : (B : ℝ) ^ 2 ≤ 529 := by nlinarith
        have : 0 ≤ (ell : ℝ) ^ 3 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by positivity
        nlinarith
      have h5 : 0 ≤ 18 * Kb * (ell : ℝ) ^ 2 * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
        unfold Kb; positivity
      nlinarith
  -- the commutator term
  set comm := lapFull (U0 L) (mulR g μ) - mulR g h with hcomm
  have hcb := comm_bound g μ (6 / ((R : ℝ) * R)) (1 / R) (by positivity) (by positivity) hglap
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
  have hsq12 : Real.sqrt 12 * ‖gradL2 (U0 L) μ‖ ≤ 9 * ((ell : ℝ) * B) * ‖h‖ := by
    have : (Real.sqrt 12 * ‖gradL2 (U0 L) μ‖) ^ 2 ≤ (9 * ((ell : ℝ) * B) * ‖h‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      have := mul_le_mul_of_nonneg_left hDμ (by norm_num : (0 : ℝ) ≤ 12)
      rw [hPdef] at this
      nlinarith [sq_nonneg ((ell : ℝ) * B * ‖h‖)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
  have hcomm_b : |⟪h, comm⟫| ≤ (36 * (ell : ℝ) ^ 2 + 9 * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
    have h1 : |⟪h, comm⟫| ≤ ‖h‖ * (6 / ((R : ℝ) * R) * ‖μ‖ + Real.sqrt 12 * (1 / R) * ‖gradL2 (U0 L) μ‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hcb hH0)
    have h2 : 6 / ((R : ℝ) * R) * ‖μ‖ ≤ 6 / ((R : ℝ) * R) * (P * ‖h‖) :=
      mul_le_mul_of_nonneg_left hμ' (by positivity)
    have h3 : Real.sqrt 12 * (1 / R) * ‖gradL2 (U0 L) μ‖ ≤ 1 / R * (9 * ((ell : ℝ) * B) * ‖h‖) := by
      have := mul_le_mul_of_nonneg_left hsq12 (by positivity : (0 : ℝ) ≤ 1 / R)
      linarith
    have e1 : ‖h‖ * (6 / ((R : ℝ) * R) * (P * ‖h‖) + 1 / R * (9 * ((ell : ℝ) * B) * ‖h‖))
        = (36 * (ell : ℝ) ^ 2 * ((B : ℝ) / R) + 9 * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
      rw [hPdef]; field_simp; ring
    have h4 : (36 * (ell : ℝ) ^ 2 * ((B : ℝ) / R) + 9 * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2
        ≤ (36 * (ell : ℝ) ^ 2 + 9 * ell) * ((B : ℝ) / R) * ‖h‖ ^ 2 := by
      have : 36 * (ell : ℝ) ^ 2 * ((B : ℝ) / R) ≤ 36 * (ell : ℝ) ^ 2 :=
        mul_le_of_le_one_right (by positivity) hBR
      have h0 : 0 ≤ ((B : ℝ) / R) * ‖h‖ ^ 2 := by positivity
      nlinarith
    calc |⟪h, comm⟫| ≤ _ := h1
      _ ≤ ‖h‖ * (6 / ((R : ℝ) * R) * (P * ‖h‖) + 1 / R * (9 * ((ell : ℝ) * B) * ‖h‖)) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 h3) hH0
      _ = _ := e1
      _ ≤ _ := h4
  -- assemble
  have hS : ∑ x, g x * ‖h x‖ ^ 2 = T1 - ⟪h, comm⟫ := by
    have e1 : ∑ x, g x * ‖h x‖ ^ 2 = ⟪h, mulR g h⟫ := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [mulR_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have e2 : mulR g h = lapFull (U0 L) (mulR g μ) - comm := by rw [hcomm]; abel
    rw [e1, e2, inner_sub_right, ← lapFull_symm (U0 L) h (mulR g μ), ← hk, hT1eq]
  rw [hS]
  unfold CA
  have := abs_le.mp hT1b
  have := abs_le.mp hcomm_b
  nlinarith

end Classes

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.norm_mulR_le
#print axioms AdalyFormal.M1Decay.poinc_cons
#print axioms AdalyFormal.M1Decay.Classes.anc_mem
#print axioms AdalyFormal.M1Decay.Classes.S_bound
