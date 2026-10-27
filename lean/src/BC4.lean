import BC3

/-!
# BC4 -- the telescoped bond-composite drift on the full tower, and `hm`

* `seq_bound`: the abstract recursion `F_{j+1} ≤ (r+θ_j)F_j`, `G_{j+1} ≤ rG_j + θ_jF_j`, `G_0 = 0` gives
  `F_j ≤ r^j e^{S_j/r} X`, `G_j ≤ r^j (S_j/r) e^{S_j/r} X`, `S_j = Σ_{i<j} θ_i`.
* `tower_FG`: on the full tower `L = scaleUp ell k Lu`, `bg = bgTower (GF) U`, flat tower `fun _ => 1`: the sequences
  `F_j = nrm (ell^j) Y_j^U`, `G_j = nrm (ell^j) (Y_j^U - Y_j^1)` satisfy the recursion for `j < k` (BC3 `step_bounds`),
  with `θ_j = thetaOf ell (ε_j)`, `ε_j` the tower-class link bound on the `ell^j`-aligned bonds of `bg j`.
* `hm_of_tower`: the exact `hm` premise of `ginv_coercive_FE_named2`, with `δm² = a/ell^k · (r^k (S_k/r) e^{S_k/r})²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

/-! ## the abstract recursion -/

theorem seq_bound (K : ℕ) (r : ℝ) (hr : 0 < r) (θ F G : ℕ → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (hθ : ∀ j, j < K → 0 ≤ θ j) (hF0 : F 0 ≤ X) (hG0 : G 0 = 0)
    (hF : ∀ j, j < K → F (j + 1) ≤ (r + θ j) * F j)
    (hG : ∀ j, j < K → G (j + 1) ≤ r * G j + θ j * F j) :
    ∀ j, j ≤ K → F j ≤ r ^ j * Real.exp ((∑ i ∈ Finset.range j, θ i) / r) * X
      ∧ G j ≤ r ^ j * ((∑ i ∈ Finset.range j, θ i) / r) * Real.exp ((∑ i ∈ Finset.range j, θ i) / r) * X := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · simpa using hF0
    · simp [hG0]
  | succ j ih =>
    intro hj
    obtain ⟨ihF, ihG⟩ := ih (by omega)
    have hjK : j < K := hj
    set S := ∑ i ∈ Finset.range j, θ i with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i hi => hθ i (by have := Finset.mem_range.mp hi; omega)
    have hS' : ∑ i ∈ Finset.range (j + 1), θ i = S + θ j := Finset.sum_range_succ _ _
    rw [hS']
    have hrj : 0 < r ^ j := pow_pos hr j
    have hE : 0 < Real.exp (S / r) := Real.exp_pos _
    have hexp : Real.exp ((S + θ j) / r) = Real.exp (S / r) * Real.exp (θ j / r) := by
      rw [← Real.exp_add]; congr 1; ring
    have hbase : r + θ j ≤ r * Real.exp (θ j / r) := by
      have := Real.add_one_le_exp (θ j / r)
      have h2 := mul_le_mul_of_nonneg_left this hr.le
      calc r + θ j = r * (θ j / r + 1) := by field_simp; ring
        _ ≤ _ := h2
    have hEj : Real.exp (S / r) ≤ Real.exp ((S + θ j) / r) := by
      apply Real.exp_le_exp.mpr
      have := hθ j hjK
      have : 0 ≤ θ j / r := by positivity
      have e : (S + θ j) / r = S / r + θ j / r := by ring
      linarith
    refine ⟨?_, ?_⟩
    · calc F (j + 1) ≤ (r + θ j) * F j := hF j hjK
        _ ≤ (r + θ j) * (r ^ j * Real.exp (S / r) * X) :=
            mul_le_mul_of_nonneg_left ihF (by linarith [hθ j hjK])
        _ ≤ (r * Real.exp (θ j / r)) * (r ^ j * Real.exp (S / r) * X) :=
            mul_le_mul_of_nonneg_right hbase (by positivity)
        _ = r ^ (j + 1) * Real.exp ((S + θ j) / r) * X := by rw [hexp, pow_succ]; ring
    · have h1 : G (j + 1) ≤ r * (r ^ j * (S / r) * Real.exp (S / r) * X)
          + θ j * (r ^ j * Real.exp (S / r) * X) := by
        calc G (j + 1) ≤ r * G j + θ j * F j := hG j hjK
          _ ≤ r * (r ^ j * (S / r) * Real.exp (S / r) * X) + θ j * (r ^ j * Real.exp (S / r) * X) :=
              add_le_add (mul_le_mul_of_nonneg_left ihG hr.le) (mul_le_mul_of_nonneg_left ihF (hθ j hjK))
      refine h1.trans ?_
      have e1 : r * (r ^ j * (S / r) * Real.exp (S / r) * X) + θ j * (r ^ j * Real.exp (S / r) * X)
          = r ^ j * ((S + θ j)) * Real.exp (S / r) * X := by field_simp
      rw [e1]
      calc r ^ j * (S + θ j) * Real.exp (S / r) * X
          ≤ r ^ j * (S + θ j) * Real.exp ((S + θ j) / r) * X := by
            have : 0 ≤ r ^ j * (S + θ j) := by have := hθ j hjK; positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEj this) hX
        _ = r ^ (j + 1) * ((S + θ j) / r) * Real.exp ((S + θ j) / r) * X := by
            rw [pow_succ]; field_simp

#print axioms seq_bound

end AdalyFormal.BondComposite
