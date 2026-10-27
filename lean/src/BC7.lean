import BC6

/-!
# BC7 -- explicit class constants and the discharge of `hm`, `hQdrift` in `ginv_coercive_FE_named2`

Class parameter: `ε_j ≤ ell^j · η` (the `link_tower_na` shape `ell^j e + 3π (ell²)^j q0 ≤ ell^j (e + 3π n q0)`),
`n = ell^k`, `ρ = n η`.  Then for `ell ≥ 2`, `ε_j ≤ 1/(1000 ell⁴)`:

* `θ(ε_j) ≤ 1800 ell² ε_j`,  `S_k = Σ_{j<k} θ_j ≤ 3600 ell ρ`   (the sum is dominated by its TOP term: it is
  `Σ ell^j`, geometric upward; the normalisation `r^k = n^{-1/2}` in front of it is what makes the total uniform in `k`);
* `eps0Of ≤ 6 ρ n^{-3/2}`;
* `deltaM ≤ √a · n^{-1} · (3600 ell^{3/2} ρ) · exp(3600 ell^{3/2} ρ)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open AdalyFormal.IngredientFamilyR2
open EstimatesLayer.E1E3
open AdalyFormal.NonflatJet

theorem sqrt192_le : Real.sqrt 192 ≤ 13.86 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
theorem sqrt240_le : Real.sqrt 240 ≤ 15.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

theorem thetaOf_le (ell : ℕ) (hell : 0 < ell) (ε : ℝ) (hε : 0 ≤ ε) (hle : ε ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    thetaOf ell ε ≤ 1800 * (ell : ℝ) ^ 2 * ε := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hk := e2Majorant_numeric_bc hell ε hε hle
  have hk0 : 0 ≤ e2Majorant (rhoOf ell ε) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  unfold thetaOf
  have h1 : Real.sqrt 240 * e2Majorant (rhoOf ell ε) ≤ 15.5 * (12 * (8 * (ell : ℝ) * (6 / 5 * ε))) :=
    mul_le_mul sqrt240_le hk hk0 (by norm_num)
  have h2 : Real.sqrt 192 * ((ell : ℝ) * ε) ≤ 13.86 * ((ell : ℝ) * ε) :=
    mul_le_mul_of_nonneg_right sqrt192_le (by positivity)
  have h3 : (ell : ℝ) * (Real.sqrt 192 * ((ell : ℝ) * ε) + Real.sqrt 240 * e2Majorant (rhoOf ell ε))
      ≤ (ell : ℝ) * (13.86 * ((ell : ℝ) * ε) + 15.5 * (12 * (8 * (ell : ℝ) * (6 / 5 * ε)))) :=
    mul_le_mul_of_nonneg_left (add_le_add h2 h1) hellR.le
  have hp : 0 ≤ (ell : ℝ) ^ 2 * ε := by positivity
  refine h3.trans ?_
  nlinarith [hp]

theorem rr_sq (ell : ℕ) (hell : 0 < ell) : rr ell ^ 2 = 1 / (ell : ℝ) := by
  unfold rr; exact Real.sq_sqrt (by positivity)

theorem geom_le (ell : ℕ) (hell : 2 ≤ ell) (k : ℕ) :
    ∑ j ∈ Finset.range k, (ell : ℝ) ^ j ≤ 2 * (ell : ℝ) ^ k / ell := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpos : (0 : ℝ) < ell := by linarith
  have h := geom_sum_mul (ell : ℝ) k
  have hk : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, (ell : ℝ) ^ j := Finset.sum_nonneg fun j _ => by positivity
  have h1 : (∑ j ∈ Finset.range k, (ell : ℝ) ^ j) * ((ell : ℝ) / 2)
      ≤ (∑ j ∈ Finset.range k, (ell : ℝ) ^ j) * ((ell : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hsum0
  rw [le_div_iff₀ hpos]
  nlinarith [h, h1, hk]

/-- `eps0` for the class `ε_j ≤ ell^j η`: `eps0Of ≤ 6 ρ n^{-3/2}`, `ρ = n η`. -/
theorem eps0Of_le (ell k : ℕ) (hell : 2 ≤ ell) (ε : ℕ → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hε : ∀ j, j < k → ε j ≤ (ell : ℝ) ^ j * η) :
    eps0Of ell k ε ≤ 6 * ((ell : ℝ) ^ k * η) * Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3) := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold eps0Of dsum
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  have hgeom := geom_sum_mul (ell : ℝ) k
  calc ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * ε i
      ≤ ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * ((ell : ℝ) ^ i * η) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hε i (Finset.mem_range.mp hi))
          (by linarith)
    _ = 6 * η * ((∑ j ∈ Finset.range k, (ell : ℝ) ^ j) * ((ell : ℝ) - 1)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 6 * η * ((ell : ℝ) ^ k - 1) := by rw [hgeom]
    _ ≤ 6 * ((ell : ℝ) ^ k * η) := by nlinarith [hη]

/-- L7 witnesses: all three explicit constants vanish at the flat background (`ε = 0`). -/
theorem thetaOf_zero (ell : ℕ) (hell : 0 < ell) : thetaOf ell 0 = 0 := by
  unfold thetaOf
  rw [e2Majorant_rhoOf_zero hell]
  simp

theorem eps0Of_zero (ell k : ℕ) : eps0Of ell k (fun _ => 0) = 0 := by
  unfold eps0Of dsum
  simp

theorem deltaM_zero (ell k : ℕ) (hell : 0 < ell) (a : ℝ) : deltaM ell k a (fun _ => 0) = 0 := by
  unfold deltaM
  simp [thetaOf_zero ell hell]

theorem hsm_of_le (ell : ℕ) (hell : 0 < ell) (ε : ℝ) (hε : 0 ≤ ε) (hle : ε ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    rhoOf ell ε < Real.pi / 2 := (numeric_small hell ε hε hle).1

theorem eq_of_sq_eq'' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y :=
  le_antisymm (le_of_sq_le' hy h.le) (le_of_sq_le' hx h.ge)

/-- `S_k = Σ_{j<k} θ_j ≤ 3600 ell ρ`, `ρ = n η`. -/
theorem S_le (ell k : ℕ) (hell : 2 ≤ ell) (ε : ℕ → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hεη : ∀ j, j < k → ε j ≤ (ell : ℝ) ^ j * η)
    (hεs : ∀ j, j < k → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    ∑ i ∈ Finset.range k, thetaOf ell (ε i) ≤ 3600 * (ell : ℝ) * ((ell : ℝ) ^ k * η) := by
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hell0 : 0 < ell := by omega
  have hpos : (0 : ℝ) < ell := by linarith
  calc ∑ i ∈ Finset.range k, thetaOf ell (ε i)
      ≤ ∑ i ∈ Finset.range k, 1800 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ i * η) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik := Finset.mem_range.mp hi
        refine (thetaOf_le ell hell0 (ε i) (hε0 i hik) (hεs i hik)).trans ?_
        exact mul_le_mul_of_nonneg_left (hεη i hik) (by positivity)
    _ = 1800 * (ell : ℝ) ^ 2 * η * ∑ j ∈ Finset.range k, (ell : ℝ) ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 1800 * (ell : ℝ) ^ 2 * η * (2 * (ell : ℝ) ^ k / ell) :=
        mul_le_mul_of_nonneg_left (geom_le ell hell k) (by positivity)
    _ = 3600 * (ell : ℝ) * ((ell : ℝ) ^ k * η) := by field_simp; ring

theorem n_mul_deltaM_scale (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a) :
    (ell : ℝ) ^ k * (Real.sqrt (a / (ell : ℝ) ^ k) * rr ell ^ k) = Real.sqrt a := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  have hrr : 0 ≤ rr ell := rr_nonneg ell
  refine eq_of_sq_eq'' (by positivity) (Real.sqrt_nonneg _) ?_
  rw [Real.sq_sqrt ha]
  have h1 : (rr ell ^ k) ^ 2 = (1 / (ell : ℝ)) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul, rr_sq ell hell]
  calc ((ell : ℝ) ^ k * (Real.sqrt (a / (ell : ℝ) ^ k) * rr ell ^ k)) ^ 2
      = ((ell : ℝ) ^ k) ^ 2 * (Real.sqrt (a / (ell : ℝ) ^ k)) ^ 2 * (rr ell ^ k) ^ 2 := by ring
    _ = ((ell : ℝ) ^ k) ^ 2 * (a / (ell : ℝ) ^ k) * (1 / (ell : ℝ)) ^ k := by
        rw [Real.sq_sqrt (div_nonneg ha hn.le), h1]
    _ = a := by
        rw [one_div, inv_pow]
        field_simp

theorem phi_mono (r : ℝ) (hr : 0 < r) {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') :
    (s / r) * Real.exp (s / r) ≤ (s' / r) * Real.exp (s' / r) :=
  mul_le_mul (div_le_div_of_nonneg_right hss hr.le) (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hss hr.le))
    (Real.exp_pos _).le (div_nonneg (hs.trans hss) hr.le)

/-- `n · deltaM ≤ √a · φ(3600 ell ρ)`: the bond-composite drift `δm` is `O(ρ / n)`, i.e. `n² δm² = O(ρ²)`, uniform in `k`. -/
theorem n_deltaM_le (ell k : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hεη : ∀ j, j < k → ε j ≤ (ell : ℝ) ^ j * η)
    (hεs : ∀ j, j < k → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4)) :
    (ell : ℝ) ^ k * deltaM ell k a ε ≤
      Real.sqrt a * (((3600 * (ell : ℝ) * ((ell : ℝ) ^ k * η)) / rr ell)
        * Real.exp ((3600 * (ell : ℝ) * ((ell : ℝ) ^ k * η)) / rr ell)) := by
  have hell0 : 0 < ell := by omega
  have hellpos : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range k, thetaOf ell (ε i) :=
    Finset.sum_nonneg fun i hi => thetaOf_nonneg ell _ (hε0 i (Finset.mem_range.mp hi))
  have hSle := S_le ell k hell ε η hη hε0 hεη hεs
  have hphi := phi_mono (rr ell) hr hS0 hSle
  have hid := n_mul_deltaM_scale ell k hell0 a ha
  unfold deltaM
  calc (ell : ℝ) ^ k * (Real.sqrt (a / (ell : ℝ) ^ k) * ((rr ell) ^ k * (((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)
          * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell))))
      = ((ell : ℝ) ^ k * (Real.sqrt (a / (ell : ℝ) ^ k) * rr ell ^ k)) *
          (((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)) := by ring
    _ = Real.sqrt a * (((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)
            * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)) := by rw [hid]
    _ ≤ _ := mul_le_mul_of_nonneg_left hphi (Real.sqrt_nonneg _)

#print axioms thetaOf_le
#print axioms thetaOf_zero
#print axioms eps0Of_zero
#print axioms deltaM_zero
#print axioms hsm_of_le
#print axioms geom_le
#print axioms eps0Of_le
#print axioms S_le
#print axioms n_mul_deltaM_scale
#print axioms phi_mono
#print axioms n_deltaM_le

end AdalyFormal.BondComposite
