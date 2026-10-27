import DLR60
import GCb6

/-!
# CovE -- the source `J` is bounded by the class WITHOUT clause 3 (m2_coverage, 2026-10-14)

`Jf_class_bound` : for every `U` with `ClassCoupled ell M c k S α₀ η U` (coverage of sites and plaquettes of `Ω₀` by class
cubes, and `PerCubeRegular2`), `η = ell^{-k}`, `1 ≤ ell`, `0 ≤ α₀`, `4β ≤ 1` with `β = c M α₀`, and EVERY fine bond `b`:
`‖Jf b‖ ≤ 4 (4β + 6β² + 1024β³)`.
Only clause 1 of the plaquette's cube is used (through `PlaqGaugeAt`, the coupling theorem `ClassCoupled.plaq_gauge`);
clause 2 and clause 3 (`ddA`) are not used.  So at a bond whose `ddA` stencil lies in no class cube (CovC
`gt_edge_no_cube`), the source is still bounded by the class constant: it cannot grow at fixed class constants.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2Coverage

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 (plaqIn)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.SourceJ (FnuMu DstarDir)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.DLayer (LocRep fN_sub fN_rsmul fN_sum3 sum_ite_ne fN_zero fN_neg frobNorm_cjM)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

theorem fnuLoc_le (P : Set (PeriodicLatticePlaquette L)) (V : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc P V ν μ y) ≤ frobNorm (FnuMu V ν μ y) := by
  unfold AdalyFormal.IngredientFamily.FnuMuLoc FnuMu
  split_ifs <;> simp [fN_neg, frobNorm_nonneg]

/-- the plaquette function from clause 1 alone: if the four bonds of the plaquette `(y; ν, μ)` are gauge-trivialised by one `g`
into `exp(iηA)` with `A` Hermitian-traceless and `η ‖A‖ ≤ t ≤ 1/4`, then `‖F_{νμ}(y)‖ ≤ 4t + 6t² + 1024t³` at `U^g`. -/
theorem fnu_of_chart (U : LinkCfg L) (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (A : Bond L → Mt) {η a1 : ℝ} (hη : 0 < η) (ht4 : 4 * (η * a1) ≤ 1)
    (ν μ : Fin 3) (hνμ : ν ≠ μ) (y : PeriodicLatticeSite L)
    (hb : ∀ e : Bond L, (e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨ e = (periodicLatticeShift y μ, ν) ∨
        e = (y, μ)) →
      HT (A e) ∧ ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Mt)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧ frobNorm (A e) ≤ a1) :
    frobNorm (FnuMu (periodicGaugeTransform g U) ν μ y) ≤ 4 * (η * a1) + 6 * (η * a1) ^ 2 + 1024 * (η * a1) ^ 3 := by
  set InC : Bond L → Prop := fun e => e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨
    e = (periodicLatticeShift y μ, ν) ∨ e = (y, μ) with hInC
  have hl : LocRep (periodicGaugeTransform g U) η A a1 (2 * a1 / η) InC := by
    refine ⟨hη, fun e he => (hb e he).2.1, fun e he => (hb e he).1, fun e he => (hb e he).2.2, ?_, by linarith⟩
    intro z d d' h0 h1
    rw [fN_rsmul, abs_of_pos (inv_pos.2 hη)]
    have a := (hb _ h1).2.2
    have b := (hb _ h0).2.2
    have c := fN_sub (A (periodicLatticeShift z d', d)) (A (z, d))
    rw [div_eq_inv_mul, mul_comm (2 : ℝ) a1, ← mul_assoc]
    have hi : 0 < η⁻¹ := inv_pos.2 hη
    calc η⁻¹ * frobNorm (A (periodicLatticeShift z d', d) - A (z, d)) ≤ η⁻¹ * (a1 + a1) :=
          mul_le_mul_of_nonneg_left (by linarith) hi.le
      _ = η⁻¹ * a1 * 2 := by ring
  have b1 : InC (y, ν) := Or.inl rfl
  have b2 : InC (periodicLatticeShift y ν, μ) := Or.inr (Or.inl rfl)
  have b3 : InC (periodicLatticeShift y μ, ν) := Or.inr (Or.inr (Or.inl rfl))
  have b4 : InC (y, μ) := Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨R, hF, hR⟩ := hl.F_expand ν μ hνμ y b1 b2 b3 b4
  have hc := hl.curl_le y ν μ b1 b2 b3 b4
  have hk := hl.Kpl_le ν μ y b1 b2 b3 b4
  rw [hF]
  refine (AdalyFormal.DLayer.fN_add _ _).trans ?_
  refine (add_le_add (AdalyFormal.DLayer.fN_add _ _) le_rfl).trans ?_
  rw [fN_rsmul, abs_of_nonneg (by positivity)]
  have e1 : η ^ 2 * (2 * (2 * a1 / η)) = 4 * (η * a1) := by field_simp; ring
  have e2 : 1024 * η ^ 3 * a1 ^ 3 = 1024 * (η * a1) ^ 3 := by ring
  have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ η ^ 2)
  rw [e1] at this
  rw [e2] at hR
  linarith

/-- the polynomial is monotone on `[0, ∞)`. -/
theorem poly_mono {t β : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ β) :
    4 * t + 6 * t ^ 2 + 1024 * t ^ 3 ≤ 4 * β + 6 * β ^ 2 + 1024 * β ^ 3 := by
  have a2 : t ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ h0 h1 2
  have a3 : t ^ 3 ≤ β ^ 3 := pow_le_pow_left₀ h0 h1 3
  linarith

/-- every term `F^P_{νμ}(y)` of the localised source is bounded by the class constant (clause 1 of the plaquette's cube). -/
theorem fnuLoc_class {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hη : 0 < η) (hell : 1 ≤ ell)
    (hU : ClassCoupled ell M c k S α₀ η U) (hα : 0 ≤ α₀) (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1)
    (ν μ : Fin 3) (hνμ : ν ≠ μ) (y : PeriodicLatticeSite L) :
    frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y)
      ≤ 4 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3 := by
  set β : ℝ := (c : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hFb0 : 0 ≤ 4 * β + 6 * β ^ 2 + 1024 * β ^ 3 := by positivity
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  -- the chart of a plaquette `p ∈ plaqIn Ω₀` bounds `F` at `p`
  have key : ∀ (p : PeriodicLatticePlaquette L), p ∈ plaqIn (S.Om 0) →
      (∀ e : Bond L, (e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨ e = (periodicLatticeShift y μ, ν) ∨
        e = (y, μ)) → e ∈ periodicPlaquetteBoundaryEdges p) →
      frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y) ≤ 4 * β + 6 * β ^ 2 + 1024 * β ^ 3 := by
    intro p hp hedges
    obtain ⟨g, A, j, hA⟩ := hU.plaq_gauge p hp
    set a1 : ℝ := (c : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1) with ha1
    have hpj : (1 : ℝ) ≤ (ell : ℝ) ^ j := one_le_pow₀ hellr
    have hta : η * a1 = β * ((ell : ℝ) ^ j)⁻¹ := by
      rw [ha1, hβ, pow_one, mul_inv]; field_simp
    have ht0 : 0 ≤ η * a1 := by rw [hta]; positivity
    have htb : η * a1 ≤ β := by
      rw [hta]
      have : ((ell : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpj
      nlinarith
    have hF := fnu_of_chart U g A (a1 := a1) hη (by linarith) ν μ hνμ y (fun e he => by
      obtain ⟨h1, h2, h3⟩ := hA e (hedges e he)
      exact ⟨h1, h2, h3.le⟩)
    have hg := AdalyFormal.GaugeCov.FnuMuLoc_gauge g (plaqIn (S.Om 0)) U ν μ y
    calc frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y)
        = frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) (periodicGaugeTransform g U) ν μ y) := by
          rw [hg, frobNorm_cjM]
      _ ≤ frobNorm (FnuMu (periodicGaugeTransform g U) ν μ y) := fnuLoc_le _ _ _ _ _
      _ ≤ 4 * (η * a1) + 6 * (η * a1) ^ 2 + 1024 * (η * a1) ^ 3 := hF
      _ ≤ 4 * β + 6 * β ^ 2 + 1024 * β ^ 3 := poly_mono ht0 htb
  rcases lt_or_gt_of_ne hνμ with hlt | hgt
  · by_cases hp : ((y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) : PeriodicLatticePlaquette L) ∈ plaqIn (S.Om 0)
    · refine key _ hp (fun e he => ?_)
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton]
      rcases he with rfl | rfl | rfl | rfl <;> simp
    · have h0 : AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y = 0 := by
        unfold AdalyFormal.IngredientFamily.FnuMuLoc
        rw [dif_pos hlt, if_neg hp]
      rw [h0, fN_zero]; exact hFb0
  · by_cases hp : ((y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) : PeriodicLatticePlaquette L) ∈ plaqIn (S.Om 0)
    · refine key _ hp (fun e he => ?_)
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton]
      rcases he with rfl | rfl | rfl | rfl <;> simp
    · have h0 : AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y = 0 := by
        unfold AdalyFormal.IngredientFamily.FnuMuLoc
        rw [dif_neg (not_lt.2 hgt.le), dif_pos hgt, if_neg hp]
      rw [h0, fN_zero]; exact hFb0

/-- **the source is bounded by the class constants at every bond, clause 3 unused.** -/
theorem Jf_class_bound {ell M c k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)}
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell k Lu)) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖
      ≤ 4 * (4 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3) := by
  set Fb : ℝ := 4 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3 with hFb
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hF : ∀ ν y, ν ≠ b.2 → frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν b.2 y) ≤ Fb :=
    fun ν y h => fnuLoc_class hη hell hU hα hsm ν b.2 h y
  have hnorm := AdalyFormal.DLayer.Jf_norm (gparams ell k Lu hell S U a Lam) b
  have hOm : (gparams ell k Lu hell S U a Lam).G.Om0 = S.Om 0 := rfl
  have hUP : (gparams ell k Lu hell S U a Lam).U = U := rfl
  rw [hOm, hUP] at hnorm
  rw [hnorm]
  have hJ : frobNorm (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) U b.1 b.2) ≤ 2 * (2 * Fb) := by
    unfold AdalyFormal.IngredientFamily.JfieldLoc
    refine (fN_sum3 _).trans ?_
    rw [← sum_ite_ne b.2 (2 * Fb)]
    refine Finset.sum_le_sum (fun ν _ => ?_)
    by_cases hν : ν = b.2
    · rw [if_pos hν, if_pos hν, fN_zero]
    · rw [if_neg hν, if_neg hν]
      unfold DstarDir
      refine (fN_sub _ _).trans ?_
      have h1 : frobNorm (AdalyFormal.Balaban.CovariantOperators.conjByAmbient
          (U (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack b.1 ν, ν))⁻¹
          (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν b.2
            (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack b.1 ν)))
          = frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν b.2
            (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack b.1 ν)) := frobNorm_cjM _ _
      rw [h1]
      have a := hF ν (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack b.1 ν) hν
      have c := hF ν b.1 hν
      linarith
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt (by norm_num)
  have hdiv := div_le_self (frobNorm_nonneg (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) U b.1 b.2)) hs2
  linarith

end AdalyFormal.M2Coverage
