import NtOdd8b

/-!
# NsOdd8c -- the second blocked level at `ell²`-aligned sites: `phi2` for ODD `ell` (lane ncwdh_strong_20261017)

For `Y` with `ell² ∣ Y_μ`:  `φ₂(Y,1) = t (-1)^{Y₁} [Y₀ = c] b₂`,  `φ₂(Y,0) = t (-1)^{Y₁} d₂ ([Y₀ = c] - [(Y₀+ell²) mod N₀ = c])`,  `φ₂(Y,2) = 0`,
`b₂ = 1 - (ell-1)/ell² - (ell-1)/ell⁴`, `d₂ = (ell-1)(ell²+1)/(2 ell³)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

noncomputable def b2 (ell : ℕ) : ℝ := 1 - ((ell : ℝ) - 1) / (ell : ℝ) ^ 2 - ((ell : ℝ) - 1) / (ell : ℝ) ^ 4
noncomputable def d2 (ell : ℕ) : ℝ := ((ell : ℝ) - 1) * ((ell : ℝ) ^ 2 + 1) / (2 * (ell : ℝ) ^ 3)

theorem sum_qN_ell {ell : ℕ} (hO : ell % 2 = 1) : ∑ n ∈ Finset.range ell, (((n % 2 : ℕ)) : ℝ) = ((ell : ℝ) - 1) / 2 := by
  have h := sum_pmN ell
  have h2 : ∀ n ∈ Finset.range ell, pmN n = 1 - 2 * (((n % 2 : ℕ)) : ℝ) := by
    intro n _; rcases pmN_cases n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hO] at h
  push_cast at h
  linarith

theorem sum_pm_ell {ell : ℕ} (hO : ell % 2 = 1) : ∑ n ∈ Finset.range ell, pmN n = 1 := by
  rw [sum_pmN, hO]; norm_num

variable {ell c : ℕ}

/-- the normalised direction-1 loop at an aligned base (interior amplitudes), in terms of the step counts `a = n₀`, `b = n₁`. -/
noncomputable def W1al (c ell Y0 a b : ℕ) : ℝ :=
  (2 * (((b % 2 : ℕ)) : ℝ) * (if Y0 = c then 1 else 0) + pmN b * (if Y0 + ell * a = c then 1 else 0) - (if Y0 = c then 1 else 0)
      + pmN b * ((if Y0 = c then 1 else 0) - (if Y0 + ell * a = c then 1 else 0)) * (aInt ell + aInt ell)) +
    (Efun c ell Y0 * (((((b % 2 : ℕ)) : ℝ) * pInt ell) + (((b % 2 : ℕ) : ℝ) * pInt ell) - pInt ell) +
      pmN b * Efun c ell (Y0 + ell * a) * pInt ell)

/-- `W₁ = - (-1)^b G(a)`. -/
theorem W1al_eq (c ell Y0 a b : ℕ) :
    W1al c ell Y0 a b = - pmN b * (((if Y0 = c then (1 : ℝ) else 0) - (if Y0 + ell * a = c then 1 else 0)) * (1 - 2 * aInt ell) +
      pInt ell * (Efun c ell Y0 - Efun c ell (Y0 + ell * a))) := by
  unfold W1al
  rcases pmN_cases b with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring

/-- the direction-1 loop of `phi1o` at an `ell²`-aligned base, as a function of the step counts (interior constants). -/
theorem loop1_aligned (G : OddGeo L ell c) (t : ℝ) (Y : PeriodicLatticeSite L) (hY : ∀ μ, ell * ell ∣ (Y μ).val)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf Y ell ell) :
    loopAngG ell ell (phi1o L c ell t) Y 1 x =
      t * sgnNat (Y 1).val * W1al c ell (Y 0).val (((x 0).val - (Y 0).val) / ell) (((x 1).val - (Y 1).val) / ell) := by
  have hell : 0 < ell := by have := G.h3; omega
  have hd : ∀ μ : Fin 3, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (G.hdiv μ)
  have hYe : ∀ μ : Fin 3, ell ∣ (Y μ).val := fun μ => dvd_trans (dvd_mul_right ell ell) (hY μ)
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, heq⟩ := loop_phi1o_dir1_eq G.hN G.hO c hell t Y x hx
  have hx2 := (mem_stepBlockOf.mp hx 2)
  have e0 : ((x 0).val - (Y 0).val) / ell = n0 := by rw [hx0, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hell]
  have e1 : ((x 1).val - (Y 1).val) / ell = n1 := by rw [hx1, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hell]
  rw [e0, e1, heq]
  unfold W1al
  have hx2e : ell ∣ (x 2).val := by
    obtain ⟨h1, h2, h3⟩ := hx2
    have : (x 2).val = (Y 2).val + ((x 2).val - (Y 2).val) := by omega
    rw [this]; exact dvd_add (hYe 2) h3
  have hx1e : ell ∣ (x 1).val := by rw [hx1]; exact dvd_add (hYe 1) (dvd_mul_right ell n1)
  have hA1 : ell ∣ ((Y 1).val + ell * ell) % (L 1 + 1) := dvd_mod_pos (hd 1) (hYe 1)
  have ha1 : aAmp L ell (x 1).val (x 2).val = aInt ell := aAmp_al G.hO hell (hd 1) (hd 2) hx1e hx2e (x 1).isLt (x 2).isLt
  have ha2 : aAmp L ell ((((Y 1).val + ell * ell) % (L 1 + 1) + ell * n1) % (L 1 + 1)) (x 2).val = aInt ell :=
    aAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) hA1) hx2e (Nat.mod_lt _ (Nat.succ_pos _)) (x 2).isLt
  have hp1 : ∀ j, pAmp L ell (((Y 1).val + ell * j) % (L 1 + 1)) (x 2).val = pInt ell := fun j =>
    pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) (hYe 1)) hx2e (Nat.mod_lt _ (Nat.succ_pos _)) (x 2).isLt
  have hp2 : ∀ j, pAmp L ell ((((Y 1).val + ell * ell) % (L 1 + 1) + ell * j) % (L 1 + 1)) (x 2).val = pInt ell := fun j =>
    pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) hA1) hx2e (Nat.mod_lt _ (Nat.succ_pos _)) (x 2).isLt
  have hp3 : ∀ j, pAmp L ell (((Y 1).val + ell * j) % (L 1 + 1)) (Y 2).val = pInt ell := fun j =>
    pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) (hYe 1)) (hYe 2) (Nat.mod_lt _ (Nat.succ_pos _)) (Y 2).isLt
  have hp4 : ∀ j, pAmp L ell (((x 1).val + ell * j) % (L 1 + 1)) (x 2).val = pInt ell := fun j =>
    pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) hx1e) hx2e (Nat.mod_lt _ (Nat.succ_pos _)) (x 2).isLt
  simp only [ha1, ha2, hp1, hp2, hp3, hp4, ← Finset.sum_mul, sum_pmN, G.hO, hx0]
  push_cast
  ring

/-- the counts of hits of the layer along an aligned row: `Σ_{a<ell} [Y₀ + ell a = c] = [Y₀ = c]` (for `ell²`-aligned `Y₀` and `c`). -/
theorem sum_Tx {ell c Y0 : ℕ} (hell : 0 < ell) (hY0 : ell * ell ∣ Y0) (hc : ell * ell ∣ c) :
    ∑ a ∈ Finset.range ell, (if Y0 + ell * a = c then (1 : ℝ) else 0) = if Y0 = c then 1 else 0 := by
  have key : ∀ a ∈ Finset.range ell, (if Y0 + ell * a = c then (1 : ℝ) else 0) = if a = 0 then (if Y0 = c then 1 else 0) else 0 := by
    intro a ha
    have hal : a < ell := Finset.mem_range.mp ha
    by_cases h0 : a = 0
    · subst h0; simp
    · rw [if_neg h0]
      have : ¬ Y0 + ell * a = c := by
        intro h
        obtain ⟨u, hu⟩ := hY0
        obtain ⟨v, hv⟩ := hc
        have h1 : ell * a = ell * ell * (v - u) := by
          rw [Nat.mul_sub]; omega
        have h2 : a = ell * (v - u) := by
          have : ell * a = ell * (ell * (v - u)) := by rw [h1]; ring
          exact Nat.eq_of_mul_eq_mul_left hell this
        have : 1 ≤ v - u := by
          rcases Nat.eq_zero_or_pos (v - u) with hz | hz
          · rw [hz] at h2; omega
          · exact hz
        have : ell ≤ ell * (v - u) := Nat.le_mul_of_pos_right ell this
        omega
      rw [if_neg this]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (Finset.range ell) 0 (fun _ => (if Y0 = c then (1 : ℝ) else 0))]
  simp [hell]

theorem Efun_aligned_sum {ell c Y0 : ℕ} (hell : 0 < ell) (hY0 : ell * ell ∣ Y0) (hc : ell * ell ∣ c) :
    ∑ a ∈ Finset.range ell, Efun c ell (Y0 + ell * a) = (if Y0 = c then 1 else 0) * (1 - (ell : ℝ)) := by
  have hYe : ell ∣ Y0 := dvd_trans (dvd_mul_right ell ell) hY0
  have hce : ell ∣ c := dvd_trans (dvd_mul_right ell ell) hc
  have : ∀ a ∈ Finset.range ell, Efun c ell (Y0 + ell * a) = (if Y0 + ell * a = c then (1 : ℝ) else 0) * (1 - (ell : ℝ)) := by
    intro a _
    rw [Efun_al hell (dvd_add hYe (dvd_mul_right ell a)) hce]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, sum_Tx hell hY0 hc]

/-- **`φ₂` in direction 1 at an `ell²`-aligned site.** -/
theorem phi2_dir1 (G : OddGeo L ell c) (t : ℝ) (Y : PeriodicLatticeSite L) (hY : ∀ μ, ell * ell ∣ (Y μ).val) :
    blockAngG ell ell (phi1o L c ell t) Y 1 = t * sgnNat (Y 1).val * ((if (Y 0).val = c then (1 : ℝ) else 0) * b2 ell) := by
  have hell : 0 < ell := by have := G.h3; omega
  have hd : ∀ μ : Fin 3, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (G.hdiv μ)
  have hYe : ∀ μ : Fin 3, ell ∣ (Y μ).val := fun μ => dvd_trans (dvd_mul_right ell ell) (hY μ)
  have hfit : ∀ μ, (Y μ).val + ell * ell ≤ L μ + 1 := by
    intro μ
    obtain ⟨k, hk⟩ := hY μ
    obtain ⟨m, hm⟩ := G.hdiv μ
    have hlt := (Y μ).isLt
    have hkm : k < m := by
      by_contra hc'
      push Not at hc'
      have := Nat.mul_le_mul_left (ell * ell) hc'
      omega
    have := Nat.mul_le_mul_left (ell * ell) hkm
    rw [Nat.mul_succ] at this
    omega
  have hell1 : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  -- the segment term
  have hseg : pathAngG ell (phi1o L c ell t) Y (List.replicate ell 1) =
      t * sgnNat (Y 1).val * ((if (Y 0).val = c then (1 : ℝ) else 0) + Efun c ell (Y 0).val * pInt ell) := by
    rw [phi1o_eq_shape, seg1_shape G.hN ell ell G.hO t _ _ _ _ _ Y, sum_pm_TE]
    have hp : ∀ j, pAmp L ell (((Y 1).val + ell * j) % (L 1 + 1)) (Y 2).val = pInt ell := fun j =>
      pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) (hYe 1)) (hYe 2) (Nat.mod_lt _ (Nat.succ_pos _)) (Y 2).isLt
    simp only [hp, ← Finset.sum_mul, sum_pmN, G.hO]
    push_cast
    ring
  unfold blockAngG
  rw [hseg]
  have hsum : ∑ x ∈ stepBlockOf Y ell ell, loopAngG ell ell (phi1o L c ell t) Y 1 x =
      ∑ x ∈ stepBlockOf Y ell ell, (fun a b _ => t * sgnNat (Y 1).val * W1al c ell (Y 0).val a b)
        (((x 0).val - (Y 0).val) / ell) (((x 1).val - (Y 1).val) / ell) (((x 2).val - (Y 2).val) / ell) :=
    Finset.sum_congr rfl (fun x hx => loop1_aligned G t Y hY x hx)
  rw [hsum, sum_block_stride Y ell ell hell hfit (fun a b _ => t * sgnNat (Y 1).val * W1al c ell (Y 0).val a b)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hY0 : ell * ell ∣ (Y 0).val := hY 0
  have hcd : ell * ell ∣ c := G.hcd
  have hE0 : Efun c ell (Y 0).val = (if (Y 0).val = c then (1 : ℝ) else 0) * (1 - (ell : ℝ)) := by
    rw [Efun_al hell (hYe 0) (dvd_trans (dvd_mul_right ell ell) hcd)]
    split_ifs <;> simp
  have hb : ∀ a ∈ Finset.range ell, ∑ b ∈ Finset.range ell, (ell : ℝ) * (t * sgnNat (Y 1).val * W1al c ell (Y 0).val a b) =
      -((ell : ℝ) * (t * sgnNat (Y 1).val *
        (((if (Y 0).val = c then (1 : ℝ) else 0) - (if (Y 0).val + ell * a = c then 1 else 0)) * (1 - 2 * aInt ell) +
          pInt ell * (Efun c ell (Y 0).val - Efun c ell ((Y 0).val + ell * a))))) := by
    intro a _
    have : ∀ b ∈ Finset.range ell, (ell : ℝ) * (t * sgnNat (Y 1).val * W1al c ell (Y 0).val a b) =
        -((ell : ℝ) * (t * sgnNat (Y 1).val *
        (((if (Y 0).val = c then (1 : ℝ) else 0) - (if (Y 0).val + ell * a = c then 1 else 0)) * (1 - 2 * aInt ell) +
          pInt ell * (Efun c ell (Y 0).val - Efun c ell ((Y 0).val + ell * a))))) * pmN b := by
      intro b _
      rw [W1al_eq]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_pm_ell G.hO, mul_one]
  rw [Finset.sum_congr rfl hb]
  have hsT := sum_Tx hell hY0 hcd
  have hsE := Efun_aligned_sum hell hY0 hcd
  have hGa : ∑ a ∈ Finset.range ell, -((ell : ℝ) * (t * sgnNat (Y 1).val *
        (((if (Y 0).val = c then (1 : ℝ) else 0) - (if (Y 0).val + ell * a = c then 1 else 0)) * (1 - 2 * aInt ell) +
          pInt ell * (Efun c ell (Y 0).val - Efun c ell ((Y 0).val + ell * a))))) =
      -((ell : ℝ) * (t * sgnNat (Y 1).val *
        ((ell * (if (Y 0).val = c then (1 : ℝ) else 0) - (if (Y 0).val = c then 1 else 0)) * (1 - 2 * aInt ell) +
          pInt ell * (ell * Efun c ell (Y 0).val - (if (Y 0).val = c then 1 else 0) * (1 - (ell : ℝ)))))) := by
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum]
    congr 3
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, sub_mul, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, hsT, hsE]
  rw [hGa, hE0]
  unfold b2 aInt pInt
  by_cases hc0 : (Y 0).val = c
  · simp only [hc0, if_true]
    field_simp
    ring
  · simp only [hc0, if_false]
    ring

/-- direction-0 loop at an aligned base: independent of the step counts `n₀, n₂`. -/
noncomputable def W0al (c ell Y0 b : ℕ) : ℝ :=
  (((b % 2 : ℕ)) : ℝ) *
      ((if Y0 = c then (1 : ℝ) else 0) - (if (Y0 + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) +
    (Efun c ell Y0 - Efun c ell ((Y0 + ell * ell) % (L 0 + 1))) * ((((b % 2 : ℕ)) : ℝ) * pInt ell) +
    ((if Y0 = c then (1 : ℝ) else 0) - (if (Y0 + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) *
      (pmN b * aInt ell - aInt ell)

theorem loop0_aligned (G : OddGeo L ell c) (t : ℝ) (Y : PeriodicLatticeSite L) (hY : ∀ μ, ell * ell ∣ (Y μ).val)
    (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf Y ell ell) :
    loopAngG ell ell (phi1o L c ell t) Y 0 x =
      t * sgnNat (Y 1).val * W0al (L := L) c ell (Y 0).val (((x 1).val - (Y 1).val) / ell) := by
  have hell : 0 < ell := by have := G.h3; omega
  have hd : ∀ μ : Fin 3, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (G.hdiv μ)
  have hYe : ∀ μ : Fin 3, ell ∣ (Y μ).val := fun μ => dvd_trans (dvd_mul_right ell ell) (hY μ)
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, heq⟩ := loop_phi1o_dir0_eq G.hN G.hO c hell t Y x hx
  have e1 : ((x 1).val - (Y 1).val) / ell = n1 := by rw [hx1, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hell]
  rw [e1, heq]
  unfold W0al
  have hx2e : ell ∣ (x 2).val := by rw [hx2]; exact dvd_add (hYe 2) (dvd_mul_right ell n2)
  have hx1e : ell ∣ (x 1).val := by rw [hx1]; exact dvd_add (hYe 1) (dvd_mul_right ell n1)
  have ha1 : aAmp L ell (x 1).val (x 2).val = aInt ell := aAmp_al G.hO hell (hd 1) (hd 2) hx1e hx2e (x 1).isLt (x 2).isLt
  have ha2 : aAmp L ell (Y 1).val (Y 2).val = aInt ell := aAmp_al G.hO hell (hd 1) (hd 2) (hYe 1) (hYe 2) (Y 1).isLt (Y 2).isLt
  have hp1 : ∀ j, pAmp L ell (((Y 1).val + ell * j) % (L 1 + 1)) (x 2).val = pInt ell := fun j =>
    pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) (hYe 1)) hx2e (Nat.mod_lt _ (Nat.succ_pos _)) (x 2).isLt
  simp only [ha1, ha2, hp1, ← Finset.sum_mul, sum_pmN]

theorem W0al_eq (c ell Y0 b : ℕ) :
    W0al (L := L) c ell Y0 b = (((b % 2 : ℕ)) : ℝ) *
      (((if Y0 = c then (1 : ℝ) else 0) - (if (Y0 + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) * (1 - 2 * aInt ell) +
        (Efun c ell Y0 - Efun c ell ((Y0 + ell * ell) % (L 0 + 1))) * pInt ell) := by
  unfold W0al
  rcases pmN_cases b with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring

theorem fit_al (G : OddGeo L ell c) (Y : PeriodicLatticeSite L) (hY : ∀ μ, ell * ell ∣ (Y μ).val) :
    ∀ μ, (Y μ).val + ell * ell ≤ L μ + 1 := by
  intro μ
  obtain ⟨k, hk⟩ := hY μ
  obtain ⟨m, hm⟩ := G.hdiv μ
  have hlt := (Y μ).isLt
  have hkm : k < m := by
    by_contra hc'
    push Not at hc'
    have := Nat.mul_le_mul_left (ell * ell) hc'
    omega
  have := Nat.mul_le_mul_left (ell * ell) hkm
  rw [Nat.mul_succ] at this
  omega

/-- **`φ₂` in direction 0 at an `ell²`-aligned site.** -/
theorem phi2_dir0 (G : OddGeo L ell c) (t : ℝ) (Y : PeriodicLatticeSite L) (hY : ∀ μ, ell * ell ∣ (Y μ).val) :
    blockAngG ell ell (phi1o L c ell t) Y 0 = t * sgnNat (Y 1).val *
      (d2 ell * ((if (Y 0).val = c then (1 : ℝ) else 0) - (if ((Y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0))) := by
  have hell : 0 < ell := by have := G.h3; omega
  have hd : ∀ μ : Fin 3, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (G.hdiv μ)
  have hYe : ∀ μ : Fin 3, ell ∣ (Y μ).val := fun μ => dvd_trans (dvd_mul_right ell ell) (hY μ)
  have hfit := fit_al G Y hY
  have hell1 : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hN0 : 0 < L 0 + 1 := Nat.succ_pos _
  have hcd : ell ∣ c := dvd_trans (dvd_mul_right ell ell) G.hcd
  -- the segment term
  have hseg : pathAngG ell (phi1o L c ell t) Y (List.replicate ell 0) =
      t * sgnNat (Y 1).val * (((if (Y 0).val = c then (1 : ℝ) else 0) - (if ((Y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) *
        aInt ell) := by
    rw [phi1o_eq_shape, seg0_shape G.hN ell ell t _ _ _ _ _ Y]
    have hD : ∑ j ∈ Finset.range ell, Dfun c ell (L 0 + 1) (((Y 0).val + ell * j) % (L 0 + 1)) =
        (if (Y 0).val = c then (1 : ℝ) else 0) - (if ((Y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) := by
      rw [Dsum_tel c ell (L 0 + 1) (Y 0).val ell hN0, Nat.mod_eq_of_lt (Y 0).isLt]
    rw [hD, aAmp_al G.hO hell (hd 1) (hd 2) (hYe 1) (hYe 2) (Y 1).isLt (Y 2).isLt]
  unfold blockAngG
  rw [hseg]
  have hsum : ∑ x ∈ stepBlockOf Y ell ell, loopAngG ell ell (phi1o L c ell t) Y 0 x =
      ∑ x ∈ stepBlockOf Y ell ell, (fun _ b _ => t * sgnNat (Y 1).val * W0al (L := L) c ell (Y 0).val b)
        (((x 0).val - (Y 0).val) / ell) (((x 1).val - (Y 1).val) / ell) (((x 2).val - (Y 2).val) / ell) :=
    Finset.sum_congr rfl (fun x hx => loop0_aligned G t Y hY x hx)
  rw [hsum, sum_block_stride Y ell ell hell hfit (fun _ b _ => t * sgnNat (Y 1).val * W0al (L := L) c ell (Y 0).val b)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hY0' : ell ∣ ((Y 0).val + ell * ell) % (L 0 + 1) := dvd_mod_pos (hd 0) (hYe 0)
  have hE0 : Efun c ell (Y 0).val = (if (Y 0).val = c then (1 : ℝ) else 0) * (1 - (ell : ℝ)) := by
    rw [Efun_al hell (hYe 0) hcd]; split_ifs <;> simp
  have hE0' : Efun c ell (((Y 0).val + ell * ell) % (L 0 + 1)) =
      (if ((Y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) * (1 - (ell : ℝ)) := by
    rw [Efun_al hell hY0' hcd]; split_ifs <;> simp
  have hq : ∑ b ∈ Finset.range ell, (ell : ℝ) * (t * sgnNat (Y 1).val * W0al (L := L) c ell (Y 0).val b) =
      (ell : ℝ) * (t * sgnNat (Y 1).val *
        (((ell : ℝ) - 1) / 2 *
          (((if (Y 0).val = c then (1 : ℝ) else 0) - (if ((Y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) * (1 - 2 * aInt ell) +
            (Efun c ell (Y 0).val - Efun c ell (((Y 0).val + ell * ell) % (L 0 + 1))) * pInt ell))) := by
    have : ∀ b ∈ Finset.range ell, (ell : ℝ) * (t * sgnNat (Y 1).val * W0al (L := L) c ell (Y 0).val b) =
        (ell : ℝ) * (t * sgnNat (Y 1).val *
          ((((if (Y 0).val = c then (1 : ℝ) else 0) - (if ((Y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) * (1 - 2 * aInt ell) +
            (Efun c ell (Y 0).val - Efun c ell (((Y 0).val + ell * ell) % (L 0 + 1))) * pInt ell))) * (((b % 2 : ℕ)) : ℝ) := by
      intro b _
      rw [W0al_eq]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_qN_ell G.hO]
    ring
  rw [hq, hE0, hE0']
  unfold d2 aInt pInt
  field_simp
  ring

/-- **`φ₂` in direction 2 vanishes at an `ell²`-aligned site.** -/
theorem phi2_dir2 (G : OddGeo L ell c) (t : ℝ) (Y : PeriodicLatticeSite L) (hY : ∀ μ, ell * ell ∣ (Y μ).val) :
    blockAngG ell ell (phi1o L c ell t) Y 2 = 0 := by
  have hell : 0 < ell := by have := G.h3; omega
  have hd : ∀ μ : Fin 3, ell ∣ L μ + 1 := fun μ => dvd_trans (dvd_mul_right ell ell) (G.hdiv μ)
  have hYe : ∀ μ : Fin 3, ell ∣ (Y μ).val := fun μ => dvd_trans (dvd_mul_right ell ell) (hY μ)
  have hβ : pathAngG ell (phi1o L c ell t) Y (List.replicate ell 2) = 0 := by
    rw [phi1o_eq_shape]; exact seg2_shape ell ell t _ _ _ _ _ Y
  unfold blockAngG
  rw [hβ]
  have hz : ∀ x ∈ stepBlockOf Y ell ell, loopAngG ell ell (phi1o L c ell t) Y 2 x = 0 := by
    intro x hx
    obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, heq⟩ := loop_phi1o_dir2_eq G.hN G.hO c hell t Y x hx
    rw [heq]
    have hx2e : ell ∣ (x 2).val := by rw [hx2]; exact dvd_add (hYe 2) (dvd_mul_right ell n2)
    have hx1e : ell ∣ (x 1).val := by rw [hx1]; exact dvd_add (hYe 1) (dvd_mul_right ell n1)
    have hA2 : ell ∣ ((Y 2).val + ell * ell) % (L 2 + 1) := dvd_mod_pos (hd 2) (hYe 2)
    have hx2' : ell ∣ ((((Y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)) := dvd_mod_pos (hd 2) hA2
    have ha1 : aAmp L ell (x 1).val (x 2).val = aInt ell := aAmp_al G.hO hell (hd 1) (hd 2) hx1e hx2e (x 1).isLt (x 2).isLt
    have ha2 : aAmp L ell (x 1).val ((((Y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)) = aInt ell :=
      aAmp_al G.hO hell (hd 1) (hd 2) hx1e hx2' (x 1).isLt (Nat.mod_lt _ (Nat.succ_pos _))
    have hp1 : ∀ j, pAmp L ell (((Y 1).val + ell * j) % (L 1 + 1)) (x 2).val = pInt ell := fun j =>
      pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) (hYe 1)) hx2e (Nat.mod_lt _ (Nat.succ_pos _)) (x 2).isLt
    have hp2 : ∀ j, pAmp L ell (((Y 1).val + ell * j) % (L 1 + 1)) ((((Y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)) = pInt ell :=
      fun j => pAmp_al G.hO hell (hd 1) (hd 2) (dvd_mod_pos (hd 1) (hYe 1)) hx2' (Nat.mod_lt _ (Nat.succ_pos _)) (Nat.mod_lt _ (Nat.succ_pos _))
    simp only [ha1, ha2, hp1, hp2, sub_self, mul_zero, zero_add]
  rw [Finset.sum_eq_zero hz]
  simp

#print axioms phi2_dir0
#print axioms phi2_dir2

end AdalyFormal.CoverOmega
