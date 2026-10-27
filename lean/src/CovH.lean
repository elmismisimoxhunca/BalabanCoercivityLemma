import CovE
import M2B8

/-!
# CovH -- the stratified source bound that the printed class gives WITHOUT clause 3 (m2_coverage, 2026-10-15)

`Jf_class_strat` : under `Admissible`, `ClassCoupled ell M c k S α₀ ell^{-k} U`, `0 ≤ α₀`, `4β ≤ 1` (`β = c M α₀`),
for every fine bond `b` whose base site lies in the stratum `B^j = Ω_j \ Ω_{j+1}`:
`‖Jf b‖ ≤ 4 (2β + 6β² + 1024β³) · ell² · (ell^{2j})⁻¹`.
Clauses 1 and 2 of the cubes covering the plaquettes at `b` are used; clause 3 (`ddA`) is not.
Compare the M1 D-layer premise `DParts.hJ` (m1_dstrat DS1:117, proved from clause 3 in DS3 `Jf_strat`):
`‖Jf b‖ ≤ SJ · (ell^{bstrat b})⁻¹ ^ 3`.  At a bond whose `ddA` stencil lies in no class cube (CovC), this file's bound is what
the class supplies.
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

/-- the plaquette function inside one class cube of index `i`: `‖F‖ ≤ (2β + 6β² + 1024β³) (ell^{2i})⁻¹`. -/
theorem fnu_in_cube {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hη : 0 < η) (hell : 1 ≤ ell)
    (hU : PerCubeRegular2 ell M c k S α₀ η U) (hα : 0 ≤ α₀) (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCube ell M c k S sites i)
    (ν μ : Fin 3) (hνμ : ν ≠ μ) (y : PeriodicLatticeSite L)
    (b1 : CubeBond sites (y, ν)) (b2 : CubeBond sites (periodicLatticeShift y ν, μ))
    (b3 : CubeBond sites (periodicLatticeShift y μ, ν)) (b4 : CubeBond sites (y, μ)) :
    ∃ g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ,
      frobNorm (FnuMu (periodicGaugeTransform g U) ν μ y)
        ≤ (2 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3) * ((ell : ℝ) ^ (2 * i))⁻¹ := by
  obtain ⟨g, A, h1, h2, -⟩ := hU sites i hq
  set β : ℝ := (c : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi : (1 : ℝ) ≤ (ell : ℝ) ^ i := one_le_pow₀ hellr
  set q : ℝ := ((ell : ℝ) ^ i * η)⁻¹ with hq'
  have hηq : η * q = ((ell : ℝ) ^ i)⁻¹ := by
    rw [hq', mul_inv]; field_simp
  have hs0 : 0 ≤ ((ell : ℝ) ^ i)⁻¹ := by positivity
  have hs1 : ((ell : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
  have hl : LocRep (periodicGaugeTransform g U) η A (β * q ^ 1) (β * q ^ 2) (CubeBond sites) := by
    refine ⟨hη, fun e he => (h1 e he).2.1, fun e he => (h1 e he).1, fun e he => (h1 e he).2.2.le,
      fun z d d' h0 h1' => (h2 d' d z h0 h1').le, ?_⟩
    have : 4 * η * (β * q ^ 1) = 4 * β * ((ell : ℝ) ^ i)⁻¹ := by rw [pow_one, ← hηq]; ring
    rw [this]
    have : 4 * β * ((ell : ℝ) ^ i)⁻¹ ≤ 4 * β * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
    linarith
  refine ⟨g, ?_⟩
  obtain ⟨R, hF, hR⟩ := hl.F_expand ν μ hνμ y b1 b2 b3 b4
  have hc := hl.curl_le y ν μ b1 b2 b3 b4
  have hk := hl.Kpl_le ν μ y b1 b2 b3 b4
  rw [hF]
  refine (AdalyFormal.DLayer.fN_add _ _).trans ?_
  refine (add_le_add (AdalyFormal.DLayer.fN_add _ _) le_rfl).trans ?_
  rw [fN_rsmul, abs_of_nonneg (by positivity)]
  set s : ℝ := ((ell : ℝ) ^ i)⁻¹ with hs
  have e2 : ((ell : ℝ) ^ (2 * i))⁻¹ = s ^ 2 := by rw [hs, pow_mul', inv_pow]
  have ea : η ^ 2 * (2 * (β * q ^ 2)) = 2 * β * s ^ 2 := by rw [← hηq]; ring
  have eb : 6 * (η * (β * q ^ 1)) ^ 2 = 6 * β ^ 2 * s ^ 2 := by rw [pow_one, ← hηq]; ring
  have ec : 1024 * η ^ 3 * (β * q ^ 1) ^ 3 = 1024 * β ^ 3 * s ^ 3 := by rw [pow_one, ← hηq]; ring
  have hcs := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ η ^ 2)
  rw [ea] at hcs
  rw [eb] at hk
  rw [ec] at hR
  have s3 : s ^ 3 ≤ s ^ 2 := by
    have : s ^ 3 = s ^ 2 * s := by ring
    rw [this]; exact mul_le_of_le_one_right (by positivity) hs1
  have hb3 : 0 ≤ β ^ 3 := by positivity
  rw [e2]
  nlinarith

/-- index of a class cube containing a site of stratum `j`: `j ≤ i + 1`. -/
theorem cube_index_ge {ell M R c k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCube ell M c k S sites i)
    {x : PeriodicLatticeSite L} (hx : x ∈ sites) {j : ℕ} (hj : x ∈ towerBj S j) : j ≤ i + 1 := by
  rcases hq.1.2.2.1 hx with h | h
  · by_contra hc
    exact AdalyFormal.M2Bridge.towerBj_disjoint' hS (show i < j by omega) h hj
  · by_contra hc
    exact AdalyFormal.M2Bridge.towerBj_disjoint' hS (show i + 1 < j by omega) h hj

/-- every term of the localised source at a site of stratum `j`. -/
theorem fnuLoc_strat {ell M R c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} (hη : 0 < η) (hell : 1 ≤ ell)
    (hS : Admissible ell M R k S) (hU : ClassCoupled ell M c k S α₀ η U) (hα : 0 ≤ α₀)
    (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1) (ν μ : Fin 3) (hνμ : ν ≠ μ) (y x : PeriodicLatticeSite L) {j : ℕ}
    (hj : x ∈ towerBj S j)
    (hxp : ∀ (p : PeriodicLatticePlaquette L), (∀ e : Bond L, (e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨
        e = (periodicLatticeShift y μ, ν) ∨ e = (y, μ)) → e ∈ periodicPlaquetteBoundaryEdges p) →
      ∀ sites : Set (PeriodicLatticeSite L), (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e) → x ∈ sites) :
    frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y)
      ≤ (2 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3) * (ell : ℝ) ^ 2
        * ((ell : ℝ) ^ (2 * j))⁻¹ := by
  set β : ℝ := (c : ℝ) * M * α₀ with hβ
  set C : ℝ := 2 * β + 6 * β ^ 2 + 1024 * β ^ 3 with hC
  have hβ0 : 0 ≤ β := by positivity
  have hC0 : 0 ≤ C := by positivity
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hell0 : (0 : ℝ) < ell := by linarith
  have hRHS0 : 0 ≤ C * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * j))⁻¹ := by positivity
  have key : ∀ (p : PeriodicLatticePlaquette L), p ∈ plaqIn (S.Om 0) →
      (∀ e : Bond L, (e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨ e = (periodicLatticeShift y μ, ν) ∨
        e = (y, μ)) → e ∈ periodicPlaquetteBoundaryEdges p) →
      frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y)
        ≤ C * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * j))⁻¹ := by
    intro p hp hedges
    obtain ⟨sites, i, hq, hcb⟩ := hU.1.2 p hp
    have hcb' : ∀ e : Bond L, (e = (y, ν) ∨ e = (periodicLatticeShift y ν, μ) ∨ e = (periodicLatticeShift y μ, ν) ∨
        e = (y, μ)) → CubeBond sites e := fun e he => hcb e (hedges e he)
    obtain ⟨g, hg⟩ := fnu_in_cube hη hell hU.2 hα hsm hq ν μ hνμ y
      (hcb' _ (Or.inl rfl)) (hcb' _ (Or.inr (Or.inl rfl))) (hcb' _ (Or.inr (Or.inr (Or.inl rfl))))
      (hcb' _ (Or.inr (Or.inr (Or.inr rfl))))
    have hij : j ≤ i + 1 := cube_index_ge hS hq (hxp p hedges sites hcb) hj
    -- `(ell^{2i})⁻¹ ≤ ell² (ell^{2j})⁻¹`
    have hpow : ((ell : ℝ) ^ (2 * i))⁻¹ ≤ (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * j))⁻¹ := by
      have h1 : (ell : ℝ) ^ (2 * j) ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * i) := by
        rw [← pow_add]; exact pow_le_pow_right₀ hellr (by omega)
      have hp1 : 0 < (ell : ℝ) ^ (2 * i) := by positivity
      have hp2 : 0 < (ell : ℝ) ^ (2 * j) := by positivity
      rw [inv_le_iff_one_le_mul₀ hp1]
      calc (1 : ℝ) = (ell : ℝ) ^ (2 * j) * ((ell : ℝ) ^ (2 * j))⁻¹ := by field_simp
        _ ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * i) * ((ell : ℝ) ^ (2 * j))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * j))⁻¹ * (ell : ℝ) ^ (2 * i) := by ring
    have hgauge := AdalyFormal.GaugeCov.FnuMuLoc_gauge g (plaqIn (S.Om 0)) U ν μ y
    calc frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y)
        = frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) (periodicGaugeTransform g U) ν μ y) := by
          rw [hgauge, frobNorm_cjM]
      _ ≤ frobNorm (FnuMu (periodicGaugeTransform g U) ν μ y) := fnuLoc_le _ _ _ _ _
      _ ≤ C * ((ell : ℝ) ^ (2 * i))⁻¹ := hg
      _ ≤ C * ((ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * j))⁻¹) := mul_le_mul_of_nonneg_left hpow hC0
      _ = C * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ (2 * j))⁻¹ := by ring
  rcases lt_or_gt_of_ne hνμ with hlt | hgt
  · by_cases hp : ((y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) : PeriodicLatticePlaquette L) ∈ plaqIn (S.Om 0)
    · refine key _ hp (fun e he => ?_)
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton]
      rcases he with rfl | rfl | rfl | rfl <;> simp
    · have h0 : AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y = 0 := by
        unfold AdalyFormal.IngredientFamily.FnuMuLoc
        rw [dif_pos hlt, if_neg hp]
      rw [h0, fN_zero]; exact hRHS0
  · by_cases hp : ((y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) : PeriodicLatticePlaquette L) ∈ plaqIn (S.Om 0)
    · refine key _ hp (fun e he => ?_)
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton]
      rcases he with rfl | rfl | rfl | rfl <;> simp
    · have h0 : AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν μ y = 0 := by
        unfold AdalyFormal.IngredientFamily.FnuMuLoc
        rw [dif_neg (not_lt.2 hgt.le), dif_pos hgt, if_neg hp]
      rw [h0, fN_zero]; exact hRHS0

/-- **the stratified source bound from the class without clause 3.** -/
theorem Jf_class_strat {ell M R c k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    (hU : ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((c : ℝ) * M * α₀) ≤ 1)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (b : Bond (scaleUp ell k Lu)) {j : ℕ} (hj : b.1 ∈ towerBj S j) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖
      ≤ 4 * ((2 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3) * (ell : ℝ) ^ 2
        * ((ell : ℝ) ^ (2 * j))⁻¹) := by
  set Fb : ℝ := (2 * ((c : ℝ) * M * α₀) + 6 * ((c : ℝ) * M * α₀) ^ 2 + 1024 * ((c : ℝ) * M * α₀) ^ 3) * (ell : ℝ) ^ 2
    * ((ell : ℝ) ^ (2 * j))⁻¹ with hFb
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hell1 : 1 ≤ ell := hell
  -- `b.1` is a corner of both plaquettes `(b.1 - ν; ν, μ)` and `(b.1; ν, μ)`
  have hF : ∀ ν y, ν ≠ b.2 → (y = b.1 ∨ y = AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack b.1 ν) →
      frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn (S.Om 0)) U ν b.2 y) ≤ Fb := by
    intro ν y hν hy
    refine fnuLoc_strat hη hell1 hS hU hα hsm ν b.2 hν y b.1 hj (fun p hedges sites hcb => ?_)
    rcases hy with rfl | rfl
    · exact (hcb _ (hedges _ (Or.inr (Or.inr (Or.inr rfl))))).1
    · have h := (hcb _ (hedges _ (Or.inl rfl))).2
      rwa [AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShift_shiftBack] at h
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
      have a := hF ν _ hν (Or.inr rfl)
      have c := hF ν b.1 hν (Or.inl rfl)
      linarith
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt (by norm_num)
  have hdiv := div_le_self (frobNorm_nonneg (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) U b.1 b.2)) hs2
  linarith

end AdalyFormal.M2Coverage
