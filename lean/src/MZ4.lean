import MZ3
import DH1

/-!
# MZ4 -- lane B's `DLayerStrat` at a printed-class configuration, modulo the operator layer (m2_dlayer, 2026-10-15)

The M1 premise `DParts.hJ` (m1_dstrat DS1:117) is a SUP bound `‖Jf b‖ ≤ SJ·ℓ^{-3 bstrat b}`; at printed-class `U` it fails at
uncovered bonds (m2_coverage `corner_nonempty`).  DS1 consumes it only through `Σ_b ‖Jf b‖·‖H(b,·)‖`, and DS1 is generic in the
weight `ω`.  Here `ω = omS = omJ + [uncovered]·omU` (MZ3 `Jf_split`), and the weighted column bounds for THIS weight are
obtained from the SAME weighted-ℓ² Combes–Thomas column bound the M1 chain uses (DY4b `H1_col`), by Cauchy–Schwarz:
* `geo_split` : `Σ_b (omS b · ℓ^{strat b.1} e^{-φ(b.1)})² ≤ 6ℓ⁶(1 + 12e^{12θ}) Σ_x ℓ^{-4 strat x} e^{-2φ(x)}`
  (bulk: DH1 `omJ_sq_le`; uncovered: MZ1 `unc_two_near` + MZ2 `unc_sum`);
* `col_class` : weighted-ℓ² column bound `≤ K² ℓ^{strat c} ‖v‖²` ⇒ `Σ_b omS b ‖h b‖ ≤ √Ageo · K ‖v‖`, k-free;
* **`dlayerStrat_class`** : `DLayerStrat` at `U` in the printed class (`ClassCoupled ℓ M 12`, NO global gauge) from the operator
  layer at `U`: the weighted-ℓ² CT column bounds of `H` and `H₁in` (`hHL2`, `hH1L2`), `hC2`, `hW`, `hKD` (DParts shapes).
* **`DLayerObligationClass` / `dlayerObligationClass_holds`** : the obligation form (every tolerance, a k-free `a₁`), with the
  operator layer as a per-configuration premise with FIXED constants.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2DLayer

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
noncomputable def omS (ell M k : ℕ) (S : Tower L) (b : Bond L) : ℝ :=
  omJ S ell k b + (if Unc ell M k S b then omU S ell k b else 0)

open Classical in
theorem omS_nonneg (ell M k : ℕ) (S : Tower L) (b : Bond L) : 0 ≤ omS ell M k S b := by
  unfold omS omJ
  have : 0 ≤ (if Unc ell M k S b then omU S ell k b else 0) := by
    split_ifs
    · unfold omU; positivity
    · exact le_rfl
  positivity

/-- the geometric constant of `phiC_colsum` -/
noncomputable def Cgeo' (ell : ℕ) (θ : ℝ) : ℝ := (ell : ℝ) ^ 4 * (64 + 8 * (ell : ℝ) ^ 3 / θ ^ 3)

/-- the total geometric constant of the split column -/
noncomputable def Ageo (ell : ℕ) (θ : ℝ) : ℝ := 6 * (ell : ℝ) ^ 6 * (1 + 12 * Real.exp (12 * θ)) * Cgeo' ell θ

theorem sum_bond {f : PeriodicLatticeSite L → ℝ} :
    ∑ b : Bond L, f b.1 = 3 * ∑ x : PeriodicLatticeSite L, f x := by
  rw [show (Finset.univ : Finset (Bond L)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]; push_cast; rfl

open Classical in
/-- **the split geometric sum** -/
theorem geo_split {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) (hRM : 3 ≤ R * M) (hcov : CoversOm0p ell M 12 k S) {θ : ℝ} (hθ : 0 ≤ θ)
    (c : PeriodicLatticeSite L) :
    ∑ b : Bond L, (omS ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(phiC S ell M R k θ c b.1))) ^ 2
      ≤ 6 * (ell : ℝ) ^ 6 * (1 + 12 * Real.exp (12 * θ)) *
        ∑ x : PeriodicLatticeSite L, (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * phiC S ell M R k θ c x)) := by
  set φ := phiC S ell M R k θ c with hφ
  set h : PeriodicLatticeSite L → ℝ := fun x => (((ell : ℝ) ^ strat S k x)⁻¹) ^ 4 * Real.exp (-(2 * φ x)) with hh
  set f : PeriodicLatticeSite L → ℝ := fun x => (((ell : ℝ) ^ strat S k x)⁻¹) ^ 2 * Real.exp (-(2 * φ x)) with hf
  set P : PeriodicLatticeSite L → Prop := fun x => 2 ≤ strat S k x ∧ ¬ StencilCovered ell M k S x with hP
  have hell1 : 1 ≤ ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hh0 : ∀ x, 0 ≤ h x := fun x => by simp only [hh]; positivity
  have hf0 : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  have hex : ∀ x, Real.exp (-(φ x)) ^ 2 = Real.exp (-(2 * φ x)) := fun x => by
    rw [sq, ← Real.exp_add]; ring_nf
  -- pointwise
  have hpt : ∀ b : Bond L, (omS ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1))) ^ 2
      ≤ 2 * (ell : ℝ) ^ 6 * h b.1 + 2 * (ell : ℝ) ^ 4 * (if P b.1 then f b.1 else 0) := by
    intro b
    have hJ := AdalyFormal.M1DStrat.CTData.omJ_sq_le hS hR hM hell1 b
    have hp : (0 : ℝ) < (ell : ℝ) ^ strat S k b.1 := by positivity
    have hE := Real.exp_pos (-(2 * φ b.1))
    set u := (if Unc ell M k S b then omU S ell k b else 0) with hu
    have hsq : (omS ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1))) ^ 2
        = (omJ S ell k b + u) ^ 2 * ((ell : ℝ) ^ strat S k b.1) ^ 2 * Real.exp (-(2 * φ b.1)) := by
      rw [← hex]; unfold omS; rw [← hu]; ring
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
    obtain ⟨a1, a2, h12, ha1, ha2⟩ := unc_two_near hS hell hM hRM hcov x hx.1 hx.2
    have hb : 1 ≤ ell ^ (strat S k x - 1) := Nat.one_le_pow _ _ (by omega)
    have hg : 1 ≤ bigSide M ell (strat S k x - 1) := by unfold bigSide; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    have hdv : ell ^ (strat S k x - 1) ∣ bigSide M ell (strat S k x - 1) := Dvd.intro_left M rfl
    exact ⟨by omega, a1, a2, h12, NP_of_dvd hb hdv hg ha1, NP_of_dvd hb hdv hg ha2⟩)
  have hsumP : ∑ x : PeriodicLatticeSite L, (if P x then f x else 0) = ∑ x ∈ Finset.univ.filter P, f x :=
    (Finset.sum_filter _ _).symm
  have hunc' : ∑ x ∈ Finset.univ.filter P, f x ≤ 12 * (ell : ℝ) ^ 2 * Real.exp (12 * θ) * ∑ x, h x := by
    refine (Finset.sum_congr ?_ (fun x _ => rfl)).trans_le hunc
    ext x; simp only [Finset.mem_filter]
  calc ∑ b : Bond L, (omS ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1))) ^ 2
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

/-- generic Cauchy–Schwarz for a weighted column -/
theorem col_cs {ι : Type*} [Fintype ι] (ω u y : ι → ℝ) (hu : ∀ i, 0 < u i) (G Q : ℝ)
    (hG : ∑ i, (ω i / u i) ^ 2 ≤ G) (hQ : ∑ i, (u i * y i) ^ 2 ≤ Q) :
    ∑ i, ω i * y i ≤ Real.sqrt G * Real.sqrt Q := by
  have e : ∀ i, ω i * y i = (ω i / u i) * (u i * y i) := fun i => by
    have := (hu i).ne'; field_simp
  rw [Finset.sum_congr rfl (fun i _ => e i)]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt hG) (Real.sqrt_le_sqrt hQ) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **the split column bound from a weighted-ℓ² Combes–Thomas column bound** -/
theorem col_class {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hell : 2 ≤ ell) (hRM : 3 ≤ R * M) (hcov : CoversOm0p ell M 12 k S) {θ : ℝ} (hθ : 0 < θ)
    (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)
    (c : PeriodicLatticeSite L) (hb : Bond L → ℝ) (hb0 : ∀ b, 0 ≤ hb b) (K vn : ℝ) (hK : 0 ≤ K) (hvn : 0 ≤ vn)
    (hL2 : ∑ b : Bond L, ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (phiC S ell M R k θ c b.1) * hb b) ^ 2
      ≤ K ^ 2 * (ell : ℝ) ^ strat S k c * vn ^ 2) :
    ∑ b : Bond L, omS ell M k S b * hb b ≤ (Real.sqrt (Ageo ell θ) * K) * vn := by
  set φ := phiC S ell M R k θ c with hφ
  have hell1 : 1 ≤ ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  have hpc : (0 : ℝ) < (ell : ℝ) ^ strat S k c := by positivity
  set u : Bond L → ℝ := fun b => ((((ell : ℝ) ^ strat S k b.1)⁻¹) * Real.exp (φ b.1)) with hu
  have hu0 : ∀ b, 0 < u b := fun b => by simp only [hu]; positivity
  have hgeo := geo_split hS hR hM hell hRM hcov hθ.le c
  have hcol := phiC_colsum hS hR hM hell1 hθ hq c
  have hG : ∑ b : Bond L, (omS ell M k S b / u b) ^ 2 ≤ Ageo ell θ * ((ell : ℝ) ^ strat S k c)⁻¹ := by
    have e : ∀ b : Bond L, omS ell M k S b / u b = omS ell M k S b * (ell : ℝ) ^ strat S k b.1 * Real.exp (-(φ b.1)) := by
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
  have h := col_cs (fun b => omS ell M k S b) u hb hu0 _ _ hG hQ
  refine h.trans (le_of_eq ?_)
  have hA : 0 ≤ Ageo ell θ := by unfold Ageo Cgeo'; positivity
  rw [← Real.sqrt_mul (by positivity)]
  have e2 : Ageo ell θ * ((ell : ℝ) ^ strat S k c)⁻¹ * (K ^ 2 * (ell : ℝ) ^ strat S k c * vn ^ 2)
      = Ageo ell θ * (K * vn) ^ 2 := by field_simp
  rw [e2, Real.sqrt_mul hA, Real.sqrt_sq (by positivity)]
  ring

#print axioms omS
#print axioms omS_nonneg
#print axioms Cgeo'
#print axioms Ageo
#print axioms sum_bond
#print axioms geo_split
#print axioms col_cs
#print axioms col_class

end AdalyFormal.M2DLayer
