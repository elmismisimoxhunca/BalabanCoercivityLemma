import ZIngredientQ1
import ZIngredientJ
import IngredientG1H1
import IngredientD2

set_option autoImplicit false
namespace Mut
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf card_blockOf witnessL witnessEll witnessY witnessY_fits)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (pathSite qOnePathSum targetCoarseBond)
open AdalyFormal.IngredientFamily

/-! ## Q1 -/
noncomputable def q1gen {Lu : PeriodicLatticeExtent} (k : ℝ) (m ell : ℕ) (A : Bond Lu → SuTwo)
    (b : CoarseBond Lu ell) : SuTwo :=
  k • ∑ x ∈ blockOf b.1.1 ell, ∑ i ∈ Finset.range m, A (pathSite x b.2 i, b.2)

theorem q1gen_const {Lu : PeriodicLatticeExtent} (k : ℝ) (m ell : ℕ) (v : SuTwo)
    (b : CoarseBond Lu ell) (hfit : ∀ ν, (b.1.1 ν).val + ell ≤ Lu ν + 1) :
    q1gen k m ell (fun _ => v) b = (k * (ell : ℝ) ^ 3 * m) • v := by
  unfold q1gen
  simp only [Finset.sum_const, Finset.card_range, card_blockOf b.1.1 ell hfit]
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  push_cast
  congr 1

-- must-not-fire: the lane's q1SU2 (== q1gen (1/ell^4) ell) maps constants to themselves
theorem q1SU2_eq_gen {Lu : PeriodicLatticeExtent} (ell : ℕ) (A : Bond Lu → SuTwo) (b : CoarseBond Lu ell) :
    q1SU2 ell A b = q1gen (1 / (ell : ℝ) ^ 4) ell ell A b := rfl

theorem q1_const_good (v : SuTwo) :
    q1SU2 witnessEll (fun _ => v) targetCoarseBond = v := by
  rw [q1SU2_eq_gen, q1gen_const _ _ _ _ _ witnessY_fits]
  have : (1 / ((witnessEll : ℕ) : ℝ) ^ 4 * (witnessEll : ℝ) ^ 3 * (witnessEll : ℕ)) = 1 := by
    have : (witnessEll : ℝ) ≠ 0 := by simp [AdalyFormal.Balaban.AdmissibleSubspace.witnessEll]
    field_simp
  rw [this, one_smul]

-- must-fire: wrong power of ell (L^{-d} instead of L^{-(d+1)})
theorem q1_bad_power (v : SuTwo) (hv : v ≠ 0) :
    q1gen (1 / (witnessEll : ℝ) ^ 3) witnessEll witnessEll (fun _ => v) targetCoarseBond ≠ v := by
  rw [q1gen_const _ _ _ _ _ witnessY_fits]
  intro h
  have e : (1 / (witnessEll : ℝ) ^ 3 * (witnessEll : ℝ) ^ 3 * (witnessEll : ℕ)) = 2 := by
    simp [AdalyFormal.Balaban.AdmissibleSubspace.witnessEll]
  rw [e] at h
  have h2 : (2:ℝ) • v - v = 0 := sub_eq_zero.mpr h
  rw [two_smul, add_sub_cancel_right] at h2
  exact hv h2

-- must-fire: path of length ell-1 instead of ell
theorem q1_bad_range (v : SuTwo) (hv : v ≠ 0) :
    q1gen (1 / (witnessEll : ℝ) ^ 4) 1 witnessEll (fun _ => v) targetCoarseBond ≠ v := by
  rw [q1gen_const _ _ _ _ _ witnessY_fits]
  intro h
  have e : (1 / (witnessEll : ℝ) ^ 4 * (witnessEll : ℝ) ^ 3 * ((1:ℕ):ℝ)) = 1/2 := by
    simp [AdalyFormal.Balaban.AdmissibleSubspace.witnessEll]; norm_num
  rw [e] at h
  have h5 : v = (1/2:ℝ) • v + (1/2:ℝ) • v := by rw [← add_smul]; norm_num
  rw [h] at h5
  apply hv
  simpa using h5

/-! ## J -/
open Matrix AdalyFormal.Balaban.SourceJ AdalyFormal.Balaban.SuTwoInner
variable {L : PeriodicLatticeExtent}

theorem JSU2_scale (η : ℝ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b : Bond L) : JSU2 η U b = ((η⁻¹ ^ 3 : ℝ)) • JSU2 1 U b := by
  apply Subtype.ext
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • Jfield U b.1 b.2 =
    ((η⁻¹ ^ 3 : ℝ) • ((-Complex.I) * (((1:ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • Jfield U b.1 b.2)
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]
  ring

/-- the law the docstring asserts: `<a, J>_hs = normalized tr (A J)` with `A = i a` (phi transport). -/
theorem J_pairing (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (a : SuTwo) (b : Bond L) :
    hsInner a (JSU2 1 U b) =
      (1/2 : ℝ) * (Matrix.trace ((Complex.I • (a : Matrix (Fin 2) (Fin 2) ℂ)) * Jfield U b.1 b.2)).re := by
  unfold hsInner
  show -(1/2:ℝ) * (Matrix.trace ((a : Matrix (Fin 2) (Fin 2) ℂ) *
      (((-Complex.I) * (((1:ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • Jfield U b.1 b.2))).re = _
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp

-- must-not-fire: lane J satisfies the pairing law (above).  must-fire: sign-flipped J does not.
theorem J_signflip_fails (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b : Bond L) (hb : JSU2 1 U b ≠ 0) :
    ∃ a : SuTwo, hsInner a (-(JSU2 1 U b)) ≠
      (1/2 : ℝ) * (Matrix.trace ((Complex.I • (a : Matrix (Fin 2) (Fin 2) ℂ)) * Jfield U b.1 b.2)).re := by
  refine ⟨JSU2 1 U b, ?_⟩
  rw [← J_pairing]
  have hpos : 0 < hsInner (JSU2 1 U b) (JSU2 1 U b) := by
    rcases lt_or_eq_of_le (hsInner_self_nonneg (JSU2 1 U b)) with h | h
    · exact h
    · exact absurd (hsInner_self_eq_zero h.symm) hb
  have : hsInner (JSU2 1 U b) (-(JSU2 1 U b)) = - hsInner (JSU2 1 U b) (JSU2 1 U b) := by
    have := hsInner_add_left
    unfold hsInner
    simp
  rw [this]
  intro h
  linarith

-- must-fire: eta-power. J(eta=2) = (1/8) J(1); a (1/4) J(1) variant is different.
theorem J_etapower_fails (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (b : Bond L) (hb : JSU2 1 U b ≠ 0) :
    ((2:ℝ)⁻¹ ^ 2 : ℝ) • JSU2 1 U b ≠ JSU2 2 U b := by
  rw [JSU2_scale 2 U b]
  intro h
  have h2 : (((2:ℝ)⁻¹ ^ 2 : ℝ) - ((2:ℝ)⁻¹ ^ 3 : ℝ)) • JSU2 1 U b = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h2 with h4 | h4
  · norm_num at h4
  · exact hb h4

/-! ## G1 -/
open scoped RealInnerProductSpace

noncomputable def toy2 : BaseData ℝ ℝ := { toyData with C2 := fun x => x ^ 2 / 4, J := 1 }

theorem toy2_K (A : ℝ) : toy2.K A = A ^ 2 / 2 := by
  have hG : toy2.Ginv = 1 := by
    simp [BaseData.Ginv, toy2, toyData]
  have hGi : toy2.G = 1 := by
    simp [BaseData.G, hG]
  have hH : toy2.H = 1 := by
    simp only [BaseData.H, hGi]
    have h1 : (toy2.Q) = 1 := rfl
    have h2 : (toy2.Qs) = 1 := rfl
    rw [h1, h2]
    change (1 * 1) * Ring.inverse ((1 * 1) * 1) = (1 : ℝ →L[ℝ] ℝ)
    simp [Ring.inverse_one]
  simp only [BaseData.K, hH]
  simp [toy2, toyData]
  ring

theorem toy2_good : toy2.IsG1inv ((1/2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) :=
  ⟨fun x y => by simp [mul_comm, mul_left_comm], fun A => by rw [toy2_K]; simp; ring⟩

-- must-fire: ignoring the C2 term (G1inv = G^{-1}) or flipping its sign is rejected.
theorem toy2_ignoreC2_fails : ¬ toy2.IsG1inv (1 : ℝ →L[ℝ] ℝ) := fun h => by
  have := h.form 1
  rw [toy2_K] at this
  first | (simp at this; done) | (simp at this; norm_num at this)

theorem toy2_signflip_fails : ¬ toy2.IsG1inv ((3/2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) := fun h => by
  have := h.form 1
  rw [toy2_K] at this
  first | (simp at this; done) | (simp at this; norm_num at this)

-- necessity of coercivity: G1inv = 0 gives a non-unit QG1Q*.
theorem unit_needs_coercivity : ¬ IsUnit ((toyData.Q.comp (toyData.G1 (0 : ℝ →L[ℝ] ℝ))).comp toyData.Qs) := by
  have : (toyData.G1 (0 : ℝ →L[ℝ] ℝ)) = 0 := by
    simp [BaseData.G1]
  rw [this]
  simp

/-! ## D2 -/
theorem D2_linear_variant_violates_law :
    ¬ (∀ (c B : ℝ), (fun B : ℝ => (ContinuousLinearMap.id ℝ ℝ) ((fun x : ℝ => x) B)) (c • B)
        = c ^ 2 • (fun B : ℝ => (ContinuousLinearMap.id ℝ ℝ) ((fun x : ℝ => x) B)) B) := by
  intro h
  have := h 2 1
  norm_num at this

theorem D2_sq_nonzero : D2unit (ContinuousLinearMap.id ℝ ℝ) (fun x : ℝ => x * x) 1 = 1 := by
  unfold D2unit
  simp [AdalyFormal.Balaban.SourceJ.Dtilde2Shape_sq]

#print axioms q1_const_good
#print axioms q1_bad_power
#print axioms q1_bad_range
#print axioms J_pairing
#print axioms J_signflip_fails
#print axioms J_etapower_fails
#print axioms toy2_good
#print axioms toy2_ignoreC2_fails
#print axioms toy2_signflip_fails
#print axioms unit_needs_coercivity
#print axioms D2_linear_variant_violates_law
#print axioms D2_sq_nonzero
end Mut
