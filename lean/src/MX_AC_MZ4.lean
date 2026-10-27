import MZ4
import MX_Base
import MX_AC_MZ1
import MX_AC_MZ3
import AC_MZ4

/-! AC copy of MZ4: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace MXP.M2DLayer
open AdalyFormal.M2DLayer

open AdalyFormal.AllC MXP.AllC
variable {Φ : Set ℕ} [CubeFactorSet Φ]

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1 (strat bstrat DLayerStrat wnormSq)
open AdalyFormal.M1DStrat (omJ phiC phiC_colsum DParts dlayerStrat_of_parts)

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the split source weight -/
noncomputable def omSACΦ (Φ : Set ℕ) (ell M k : ℕ) (S : Tower L) (b : Bond L) : ℝ :=
  omJ S ell k b + (if UncACΦ Φ ell M k S b then omU S ell k b else 0)

open Classical in
open Classical in
/-- **the split geometric sum** -/
theorem geo_splitACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) (hRM : 3 ≤ R * M) (hcov : CoversOmΦ ell M Φ k S) {θ : ℝ} (hθ : 0 ≤ θ)
    (c : PeriodicLatticeSite L) :
    ∑ b : Bond L, (omSACΦ Φ ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(phiC S ell M R k θ c b.1))) ^ 2
      ≤ 6 * (ell : ℝ) ^ 6 * (1 + 12 * Real.exp (12 * θ)) *
        ∑ x : PeriodicLatticeSite L, (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * phiC S ell M R k θ c x)) := by
  set φ := phiC S ell M R k θ c with hφ
  set h : PeriodicLatticeSite L → ℝ := fun x => (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * φ x)) with hh
  set f : PeriodicLatticeSite L → ℝ := fun x => (((ell : ℝ) ^ strat S k x)⁻¹) ^ 2 * Real.exp (-(2 * φ x)) with hf
  set P : PeriodicLatticeSite L → Prop := fun x => 2 ≤ strat S k x ∧ ¬ StencilCoveredACΦ Φ ell M k S x with hP
  have hell1 : 1 ≤ ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hh0 : ∀ x, 0 ≤ h x := fun x => by simp only [hh]; positivity
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  have hex : ∀ x, Real.exp (-(φ x)) ^ 2 = Real.exp (-(2 * φ x)) := fun x => by
    rw [sq, ← Real.exp_add]; ring_nf
  -- pointwise
  have hpt : ∀ b : Bond L, (omSACΦ Φ ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1))) ^ 2
      ≤ 2 * (ell : ℝ) ^ 6 * h b.1 + 2 * (ell : ℝ) ^ 4 * (if P b.1 then f b.1 else 0) := by
    intro b
    have hJ := AdalyFormal.M1DStrat.CTData.omJ_sq_le hS hR hM hell1 b
    have hp : (0 : ℝ) < (ell : ℝ) ^ strat S k b.1 := by positivity
    have hE := Real.exp_pos (-(2 * φ b.1))
    set u := (if UncACΦ Φ ell M k S b then omU S ell k b else 0) with hu
    have hsq : (omSACΦ Φ ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1))) ^ 2
        = (omJ S ell k b + u) ^ 2 * ((ell : ℝ) ^ strat S k b.1) ^ 2 * Real.exp (-(2 * φ b.1)) := by
      rw [← hex]; unfold omSACΦ; rw [← hu]; ring
    have hab : (omJ S ell k b + u) ^ 2 ≤ 2 * omJ S ell k b ^ 2 + 2 * u ^ 2 := by nlinarith [sq_nonneg (omJ S ell k b - u)]
    have hu2 : u ^ 2 * ((ell : ℝ) ^ strat S k b.1) ^ 2 ≤ (ell : ℝ) ^ 4 * (if P b.1 then (((ell : ℝ) ^ strat S k b.1)⁻¹) ^ 2 else 0) := by
      rw [hu]
      split_ifs with h1 h2
      · unfold omU
        rw [pow_mul']
        field_simp
        rfl
      · exact absurd ⟨le_trans h1.1 (min_le_left _ _), h1.2⟩ h2
      · norm_num <;> positivity
      · norm_num
    have hfP : (if P b.1 then f b.1 else 0) = (if P b.1 then (((ell : ℝ) ^ strat S k b.1)⁻¹) ^ 2 else 0) * Real.exp (-(2 * φ b.1)) := by
      split_ifs <;> simp [hf]
    rw [hsq, hfP]
    calc (omJ S ell k b + u) ^ 2 * ((ell : ℝ) ^ strat S k b.1) ^ 2 * Real.exp (-(2 * φ b.1))
        ≤ (2 * omJ S ell k b ^ 2 + 2 * u ^ 2) * ((ell : ℝ) ^ strat S k b.1) ^ 2 * Real.exp (-(2 * φ b.1)) := by
          gcongr
      _ = 2 * (omJ S ell k b ^ 2 * ((ell : ℝ) ^ strat S k b.1) ^ 2) * Real.exp (-(2 * φ b.1))
          + 2 * (u ^ 2 * ((ell : ℝ) ^ strat S k b.1) ^ 2) * Real.exp (-(2 * φ b.1)) := by ring
      _ ≤ 2 * ((ell : ℝ) ^ 6 * (((ell : ℝ) ^ strat S k b.1)⁻¹) ^ 4) * Real.exp (-(2 * φ b.1))
          + 2 * ((ell : ℝ) ^ 4 * (if P b.1 then (((ell : ℝ) ^ strat S k b.1)⁻¹) ^ 2 else 0)) * Real.exp (-(2 * φ b.1)) := by
          gcongr
      _ = _ := by simp only [hh]; ring
  -- sums
  have hunc := unc_sum hS hR hM hell hθ c P (fun x hx => by
    obtain ⟨a1, a2, h12, ha1, ha2⟩ := unc_two_nearACΦ hS hell hM hRM hcov x hx.1 hx.2
    have hb : 1 ≤ ell ^ (strat S k x - 1) := Nat.one_le_pow _ _ (by omega)
    have hg : 1 ≤ bigSide M ell (strat S k x - 1) := by unfold bigSide; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    have hdv : ell ^ (strat S k x - 1) ∣ bigSide M ell (strat S k x - 1) := Dvd.intro_left M rfl
    exact ⟨by omega, a1, a2, h12, NP_of_dvd hb hdv hg ha1, NP_of_dvd hb hdv hg ha2⟩)
  have hsumP : ∑ x : PeriodicLatticeSite L, (if P x then f x else 0) = ∑ x ∈ Finset.univ.filter P, f x :=
    (Finset.sum_filter _ _).symm
  have hunc' : ∑ x ∈ Finset.univ.filter P, f x ≤ 12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) * ∑ x, h x := by
    refine (Finset.sum_congr ?_ (fun x _ => rfl)).trans_le hunc
    ext x; simp only [Finset.mem_filter]
  calc ∑ b : Bond L, (omSACΦ Φ ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1))) ^ 2
      ≤ ∑ b : Bond L, (2 * (ell : ℝ) ^ 6 * h b.1 + 2 * (ell : ℝ) ^ 4 * (if P b.1 then f b.1 else 0)) :=
        Finset.sum_le_sum (fun b _ => hpt b)
    _ = 3 * ∑ x : PeriodicLatticeSite L, (2 * (ell : ℝ) ^ 6 * h x + 2 * (ell : ℝ) ^ 4 * (if P x then f x else 0)) :=
        sum_bond (f := fun x => 2 * (ell : ℝ) ^ 6 * h x + 2 * (ell : ℝ) ^ 4 * (if P x then f x else 0))
    _ = 6 * (ell : ℝ) ^ 6 * ∑ x, h x + 6 * (ell : ℝ) ^ 4 * ∑ x ∈ Finset.univ.filter P, f x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumP]; ring
    _ ≤ 6 * (ell : ℝ) ^ 6 * ∑ x, h x + 6 * (ell : ℝ) ^ 4 * (12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) * ∑ x, h x) := by
        have h6 : (0 : ℝ) ≤ 6 * (ell : ℝ) ^ 4 := by positivity
        have := mul_le_mul_of_nonneg_left hunc' h6
        linarith
    _ = 6 * (ell : ℝ) ^ 6 * (1 + 12 * Real.exp (12 * θ)) * ∑ x, h x := by ring

/-- **the split column bound from a weighted-ℓ² Combes–Thomas column bound** -/
theorem col_classACΦ {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) (hRM : 3 ≤ R * M) (hcov : CoversOmΦ ell M Φ k S) {θ : ℝ} (hθ : 0 < θ)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)
    (c : PeriodicLatticeSite L) (hb : Bond L → ℝ) (hb0 : ∀ b, 0 ≤ hb b) (K vn : ℝ) (hK : 0 ≤ K) (hvn : 0 ≤ vn)
    (hL2 : ∑ b : Bond L, ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (phiC S ell M R k θ c b.1) * hb b) ^ 2
      ≤ K ^ 2 * (ell : ℝ) ^ strat S k c * vn ^ 2) :
    ∑ b : Bond L, omSACΦ Φ ell M k S b * hb b ≤ (Real.sqrt (Ageo ell θ) * K) * vn := by
  set φ := phiC S ell M R k θ c with hφ
  have hell1 : 1 ≤ ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hpc : (0 : ℝ) < (ell : ℝ) ^ strat S k c := by positivity
  set u : Bond L → ℝ := fun b => ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (φ b.1)) with hu
  have hu0 : ∀ b, 0 < u b := fun b => by simp only [hu]; positivity
  have hgeo := geo_splitACΦ hS hR hM hell hRM hcov hθ.le c
  have hcol := phiC_colsum hS hR hM hell1 hθ hq c
  have hG : ∑ b : Bond L, (omSACΦ Φ ell M k S b / u b) ^ 2 ≤ Ageo ell θ * ((ell : ℝ) ^ strat S k c)⁻¹ := by
    have e : ∀ b : Bond L, omSACΦ Φ ell M k S b / u b = omSACΦ Φ ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1)) := by
      intro b
      simp only [hu]
      have hp : (0 : ℝ) < (ell : ℝ) ^ strat S k b.1 := by positivity
      rw [Real.exp_neg]; field_simp
    rw [Finset.sum_congr rfl (fun b _ => by rw [e b])]
    refine hgeo.trans ?_
    unfold Ageo Cgeo'
    have h0 : 0 ≤ 6 * (ell : ℝ) ^ 6 * (1 + 12 * Real.exp (12 * θ)) := by positivity
    calc 6 * (ell : ℝ) ^ 6 * (1 + 12 * Real.exp (12 * θ)) *
          ∑ x, (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * phiC S ell M R k θ c x))
        ≤ 6 * (ell : ℝ) ^ 6 * (1 + 12 * Real.exp (12 * θ)) *
          ((ell : ℝ) ^ 4 * (64 + 8 * (ell : ℝ) ^ 3 / θ ^ 3) * ((ell : ℝ) ^ strat S k c)⁻¹) :=
          mul_le_mul_of_nonneg_left hcol h0
      _ = _ := by ring
  have hQ : ∑ b : Bond L, (u b * hb b) ^ 2 ≤ K ^ 2 * (ell : ℝ) ^ strat S k c * vn ^ 2 := hL2
  have h := col_cs (fun b => omSACΦ Φ ell M k S b) u hb hu0 _ _ hG hQ
  refine h.trans (le_of_eq ?_)
  have hA : 0 ≤ Ageo ell θ := by unfold Ageo Cgeo'; positivity
  rw [← Real.sqrt_mul (by positivity)]
  have e2 : Ageo ell θ * ((ell : ℝ) ^ strat S k c)⁻¹ * (K ^ 2 * (ell : ℝ) ^ strat S k c * vn ^ 2)
      = Ageo ell θ * (K * vn) ^ 2 := by field_simp
  rw [e2, Real.sqrt_mul hA, Real.sqrt_sq (by positivity)]
  ring

end MXP.M2DLayer

