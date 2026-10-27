import DS2
import DLR60

/-!
# DS3 -- D3 `jsmooth_strat`: the source is stratum-scaled on the M1 regime (M1 D-layer lane, 2026-10-13)

For `U` in lane B's `M1Regular ell M 12 k S α₀ (ℓ^k)⁻¹` on an admissible tower with `4 ≤ R·M`, `β = 12Mα₀`, `4β ≤ 1`:
  **`Jf_strat`** : `‖(gparams ..).Jf b‖ ≤ (400·ℓ³·β) · ℓ^{-3 bstrat b}` for EVERY fine bond `b` (k-, volume-, tower-free).
Route.  Gauge covariance (GCb7 `JfieldLoc_gauge`) moves to `V = U^g = exp(iηA)` on every bond.
* `bstrat b ≤ 1` (this includes every bond near `∂Ω₀`, where `J` is TRUNCATED to `plaqIn Ω₀`): crude bound
  `‖F̃‖ ≤ ‖F‖ ≤ 2β + 6β² + 1024β³` (DL56 `F_expand` with the stratum-0 constants, valid on every bond), so `‖J‖ ≤ 4·max‖F‖`.
* `bstrat b ≥ 2`: every site within `ℓ¹`-distance 4 of `b.1` has stratum `≥ 1` (lane B `strat_close`, collar `4 ≤ RM`), hence
  lies in `Ω₀`: the truncation is invisible (`JfieldLoc = Jfield`), and every bond `J(b)` reads has `bstrat ≥ j := bstrat b − 1`;
  DL58 `LocRep.J_local_bound` with the level-`j` constants of `M1Bounds` gives `‖J‖ ≤ ℓ^{-3j}(β + 40β² + 4144β³ + 8192β⁴)`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg)
open AdalyFormal.Balaban.SourceJ (piProj FnuMu DstarDir Jfield)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.StatementLane2 (curlA ddA)
open AdalyFormal.DLayer (LocRep NeedBonds Hof Kpl fN_add fN_sub fN_neg fN_zero fN_rsmul fN_sum3 sum_ite_ne
  frobNorm_cjM)
open AdalyFormal.M1

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

/-! ## 1. distances of nearby sites -/

theorem pd_sh {x y : PeriodicLatticeSite L} {n : ℕ} (h : pdist x y ≤ n) (d : Fin 3) :
    pdist x (periodicLatticeShift y d) ≤ n + 1 := by
  have h1 := AdalyFormal.StatementLaneR8.pdist_shift_le y d
  have h2 := AdalyFormal.StatementLaneR8.pdist_triangle x y (periodicLatticeShift y d)
  omega

theorem pd_bk {x y : PeriodicLatticeSite L} {n : ℕ} (h : pdist x y ≤ n) (d : Fin 3) :
    pdist x (periodicLatticeShiftBack y d) ≤ n + 1 := by
  have h1 := AdalyFormal.StatementLaneR8.pdist_shift_le (periodicLatticeShiftBack y d) d
  rw [periodicLatticeShift_shiftBack, AdalyFormal.StatementLaneR8.pdist_comm] at h1
  have h2 := AdalyFormal.StatementLaneR8.pdist_triangle x y (periodicLatticeShiftBack y d)
  omega

theorem pd0 (x : PeriodicLatticeSite L) : pdist x x ≤ 0 := by
  rw [AdalyFormal.StatementLaneR8.pdist_self]

/-- within `ℓ¹`-distance `R M` the stratum drops by at most one -/
theorem strat_le_near {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) (hell : 1 ≤ ell)
    {x z : PeriodicLatticeSite L} (hd : pdist x z ≤ R * M) : strat S k x ≤ strat S k z + 1 := by
  refine strat_close h ?_
  rw [AdalyFormal.StatementLaneR8.pdist_comm]
  refine hd.trans (Nat.mul_le_mul_left _ ?_)
  unfold bigSide
  exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)

/-- a bond with both endpoints within distance `R M` of `x` has `bstrat ≥ strat x − 1` -/
theorem bstrat_ge_near {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) (hell : 1 ≤ ell)
    {x : PeriodicLatticeSite L} (e : Bond L) (h1 : pdist x e.1 ≤ R * M)
    (h2 : pdist x (periodicLatticeShift e.1 e.2) ≤ R * M) : strat S k x ≤ bstrat S k e + 1 := by
  unfold bstrat
  have a := strat_le_near h hell h1
  have b := strat_le_near h hell h2
  omega

/-- a site of stratum `≥ 1` lies in `Ω₀` -/
theorem mem_om0_of_strat {ell M R k : ℕ} {S : Tower L} (h : Admissible ell M R k S) {z : PeriodicLatticeSite L}
    (hz : 1 ≤ strat S k z) : z ∈ S.Om 0 :=
  om_anti h (Nat.zero_le _) (mem_strat_of_pos hz)

/-! ## 2. truncated plaquette functions -/

theorem FnuMuLoc_le (P : Set (PeriodicLatticePlaquette L)) (V : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    frobNorm (AdalyFormal.IngredientFamily.FnuMuLoc P V ν μ y) ≤ frobNorm (FnuMu V ν μ y) := by
  unfold AdalyFormal.IngredientFamily.FnuMuLoc FnuMu
  split_ifs <;> simp [fN_neg, frobNorm_nonneg]

theorem FnuMuLoc_eq (P : Set (PeriodicLatticePlaquette L)) (V : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν μ : Fin 3) (y : PeriodicLatticeSite L)
    (hP : ∀ d : PeriodicPlaquetteDirections, ((y, d) : PeriodicLatticePlaquette L) ∈ P) :
    AdalyFormal.IngredientFamily.FnuMuLoc P V ν μ y = FnuMu V ν μ y := by
  unfold AdalyFormal.IngredientFamily.FnuMuLoc FnuMu
  split_ifs <;> simp_all

/-- every plaquette based at `y` is in `plaqIn Ω` if the sites within distance 2 of `y` are -/
theorem plaq_mem_of_near (Om : Set (PeriodicLatticeSite L)) (y : PeriodicLatticeSite L)
    (hz : ∀ z, pdist y z ≤ 2 → z ∈ Om) (d : PeriodicPlaquetteDirections) :
    ((y, d) : PeriodicLatticePlaquette L) ∈ plaqIn Om := by
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
  have y0 : pdist y y ≤ 0 := pd0 y
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hz _ (y0.trans (by norm_num)), hz _ ((pd_sh y0 _).trans (by norm_num))⟩
  · exact ⟨hz _ ((pd_sh y0 _).trans (by norm_num)), hz _ ((pd_sh (pd_sh y0 _) _).trans (by norm_num))⟩
  · exact ⟨hz _ ((pd_sh y0 _).trans (by norm_num)), hz _ ((pd_sh (pd_sh y0 _) _).trans (by norm_num))⟩
  · exact ⟨hz _ (y0.trans (by norm_num)), hz _ ((pd_sh y0 _).trans (by norm_num))⟩

/-- the truncation is invisible at `x` when every site within distance 3 of `x` is in `Ω` -/
theorem JfieldLoc_eq_of_near (Om : Set (PeriodicLatticeSite L)) (V : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : PeriodicLatticeSite L) (μ : Fin 3)
    (hz : ∀ z, pdist x z ≤ 3 → z ∈ Om) :
    AdalyFormal.IngredientFamily.JfieldLoc (plaqIn Om) V x μ = Jfield V x μ := by
  have hJ : Jfield V x μ = ∑ ν : Fin 3, (if ν = μ then (0 : Mt) else DstarDir V ν (fun z => FnuMu V ν μ z) x) := rfl
  rw [hJ]
  unfold AdalyFormal.IngredientFamily.JfieldLoc
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  split_ifs with hν
  · rfl
  · unfold DstarDir
    have x0 : pdist x x ≤ 0 := pd0 x
    have e1 : AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn Om) V ν μ x = FnuMu V ν μ x :=
      FnuMuLoc_eq _ V ν μ x (plaq_mem_of_near Om x (fun z hz' => hz z (by omega)))
    have e2 : AdalyFormal.IngredientFamily.FnuMuLoc (plaqIn Om) V ν μ (periodicLatticeShiftBack x ν)
        = FnuMu V ν μ (periodicLatticeShiftBack x ν) := by
      refine FnuMuLoc_eq _ V ν μ _ (plaq_mem_of_near Om _ (fun z hz' => hz z ?_))
      have h1 := pd_bk x0 ν
      have h2 := AdalyFormal.StatementLaneR8.pdist_triangle x (periodicLatticeShiftBack x ν) z
      omega
    simp only [e1, e2]

/-- the conjugation by a link is an isometry -/
theorem frob_conjByAmbient (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (X : Mt) :
    frobNorm (AdalyFormal.Balaban.CovariantOperators.conjByAmbient g X) = frobNorm X :=
  frobNorm_cjM g X

/-- crude bound of the truncated source from a bound on the plaquette functions -/
theorem JfieldLoc_crude (P : Set (PeriodicLatticePlaquette L)) (V : PeriodicLinkConfiguration
    (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : PeriodicLatticeSite L) (μ : Fin 3) (Fb : ℝ)
    (hF : ∀ ν y, ν ≠ μ → frobNorm (FnuMu V ν μ y) ≤ Fb) :
    frobNorm (AdalyFormal.IngredientFamily.JfieldLoc P V x μ) ≤ 2 * (2 * Fb) := by
  unfold AdalyFormal.IngredientFamily.JfieldLoc
  refine (fN_sum3 _).trans ?_
  rw [← sum_ite_ne μ (2 * Fb)]
  refine Finset.sum_le_sum (fun ν _ => ?_)
  by_cases hν : ν = μ
  · rw [if_pos hν, if_pos hν, fN_zero]
  · rw [if_neg hν, if_neg hν]
    unfold DstarDir
    refine (fN_sub _ _).trans ?_
    rw [frob_conjByAmbient]
    have a := (FnuMuLoc_le P V ν μ (periodicLatticeShiftBack x ν)).trans (hF ν _ hν)
    have b := (FnuMuLoc_le P V ν μ x).trans (hF ν x hν)
    linarith

/-! ## 3. the local representation from `M1Bounds` -/

/-- the level-`j` local representation: on the bonds of `bstrat ≥ j`, constants `β q`, `β q²`, `q = (ℓ^j η)⁻¹`. -/
theorem locRep_of_M1 {S : Tower L} {ell M f k : ℕ} {α₀ η : ℝ} (hη : 0 < η) (hell : 1 ≤ ell)
    {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} {A : Bond L → Mt}
    (hU : ∀ e : Bond L, ((V e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Mt) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (j : ℕ) (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1) :
    LocRep V η A ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2))
      (fun e => j ≤ bstrat S k e) := by
  obtain ⟨hHT, h1, h2, -⟩ := hB
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpj : (1 : ℝ) ≤ (ell : ℝ) ^ j := one_le_pow₀ hellr
  refine ⟨hη, fun e _ => hU e, fun e _ => hHT e, fun e he => (h1 e j he).le, fun z d d' h0 h1' => (h2 d' d z j h0 h1').le, ?_⟩
  -- smallness `4 η a₁ ≤ 1`
  have hβ0 : 0 ≤ (f : ℝ) * M * α₀ := by
    by_contra hneg
    push Not at hneg
    have := h1 (Classical.arbitrary _) 0 (Nat.zero_le _)
    have hq : 0 < (((ell : ℝ) ^ 0 * η)⁻¹ ^ 1) := by positivity
    nlinarith [frobNorm_nonneg (A (Classical.arbitrary (Bond L)))]
  have e : η * ((((ell : ℝ) ^ j * η)⁻¹) ^ 1) = ((ell : ℝ) ^ j)⁻¹ := by
    rw [pow_one, mul_inv, mul_comm ((ell : ℝ) ^ j)⁻¹, ← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul]
  have ht : ((ell : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpj
  have : 4 * η * ((f : ℝ) * M * α₀ * ((((ell : ℝ) ^ j * η)⁻¹) ^ 1))
      = 4 * ((f : ℝ) * M * α₀) * ((ell : ℝ) ^ j)⁻¹ := by rw [← e]; ring
  rw [this]
  have : 4 * ((f : ℝ) * M * α₀) * ((ell : ℝ) ^ j)⁻¹ ≤ 4 * ((f : ℝ) * M * α₀) * 1 :=
    mul_le_mul_of_nonneg_left ht (by positivity)
  linarith

/-- the plaquette function is `O(β)` on every plaquette (stratum-0 constants) -/
theorem FnuMu_crude {S : Tower L} {ell M f k : ℕ} {α₀ η : ℝ} (hη : 0 < η) (hell : 1 ≤ ell)
    {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} {A : Bond L → Mt}
    (hU : ∀ e : Bond L, ((V e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Mt) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1Bounds S ell M f k α₀ η A) (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1) (ν μ : Fin 3) (hνμ : ν ≠ μ)
    (y : PeriodicLatticeSite L) :
    frobNorm (FnuMu V ν μ y) ≤ 2 * ((f : ℝ) * M * α₀) + 6 * ((f : ℝ) * M * α₀) ^ 2 + 1024 * ((f : ℝ) * M * α₀) ^ 3 := by
  have hl := locRep_of_M1 hη hell hU hB 0 hsm
  set β := (f : ℝ) * M * α₀ with hβ
  have hq : (((ell : ℝ) ^ 0 * η)⁻¹) = η⁻¹ := by rw [pow_zero, one_mul]
  have z : ∀ e : Bond L, 0 ≤ bstrat S k e := fun _ => Nat.zero_le _
  obtain ⟨R, hF, hR⟩ := hl.F_expand ν μ hνμ y (z _) (z _) (z _) (z _)
  rw [hF]
  have hc := hl.curl_le y ν μ (z _) (z _) (z _) (z _)
  have hk := hl.Kpl_le ν μ y (z _) (z _) (z _) (z _)
  rw [hq] at hc hk hR
  have ea : η * (β * η⁻¹ ^ 1) = β := by field_simp
  have eb : η ^ 2 * (2 * (β * η⁻¹ ^ 2)) = 2 * β := by field_simp
  have ec : η ^ 3 * (β * η⁻¹ ^ 1) ^ 3 = β ^ 3 := by field_simp
  rw [ea] at hk
  have hR' : frobNorm R ≤ 1024 * β ^ 3 := by
    have : 1024 * η ^ 3 * (β * η⁻¹ ^ 1) ^ 3 = 1024 * β ^ 3 := by rw [mul_assoc, ec]
    linarith
  refine (fN_add _ _).trans ?_
  refine (add_le_add (fN_add _ _) hR').trans ?_
  rw [fN_rsmul, abs_of_nonneg (by positivity)]
  have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ η ^ 2)
  linarith

/-! ## 4. D3 -/

/-- the `J`-polynomial of the class, as a multiple of `β` for `4β ≤ 1` -/
theorem jpoly_le (β : ℝ) (h0 : 0 ≤ β) (h1 : 4 * β ≤ 1) :
    β + 40 * β ^ 2 + 4144 * β ^ 3 + 8192 * β ^ 4 ≤ 398 * β := by
  have hb : β ≤ 1 / 4 := by linarith
  have a2 : β ^ 2 ≤ β * (1 / 4) := by nlinarith
  have a3 : β ^ 3 ≤ β * (1 / 16) := by nlinarith [pow_le_pow_left₀ h0 hb 2]
  have a4 : β ^ 4 ≤ β * (1 / 64) := by nlinarith [pow_le_pow_left₀ h0 hb 3]
  nlinarith

/-- **D3** (`jsmooth_strat`) at one configuration of the M1 regime. -/
theorem Jf_strat (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (α₀ : ℝ)
    (hA : Admissible ell M R k S) (hRM : 4 ≤ R * M)
    (hU : M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    (b : Bond (scaleUp ell k Lu)) :
    ‖(gparams ell k Lu hell S U a Lam).Jf b‖ ≤ (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀)) * omJ S ell k b := by
  obtain ⟨g, A, hrep, hB⟩ := hU
  have hell1 : 1 ≤ ell := hell
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast hell1
  set η : ℝ := ((ell : ℝ) ^ k)⁻¹ with hηdef
  have hη : 0 < η := by positivity
  have hf : ((12 : ℕ) : ℝ) = 12 := by norm_num
  set β : ℝ := (12 : ℝ) * M * α₀ with hβdef
  have hsm' : 4 * (((12 : ℕ) : ℝ) * M * α₀) ≤ 1 := by rw [hf]; exact hsm
  set V := periodicGaugeTransform g U with hV
  -- ‖Jf b‖ in terms of `V`
  have hnorm := AdalyFormal.DLayer.Jf_norm (gparams ell k Lu hell S U a Lam) b
  have hOm : (gparams ell k Lu hell S U a Lam).G.Om0 = S.Om 0 := rfl
  rw [hOm] at hnorm
  have hg := AdalyFormal.GaugeCov.JfieldLoc_gauge g (plaqIn (S.Om 0)) U b.1 b.2
  have hfV : frobNorm (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) V b.1 b.2)
      = frobNorm (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) U b.1 b.2) := by
    rw [hV, hg, frobNorm_cjM]
  have hUP : (gparams ell k Lu hell S U a Lam).U = U := rfl
  rw [hUP, ← hfV] at hnorm
  rw [hnorm]
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]; exact Real.sqrt_le_sqrt (by norm_num)
  have hdiv : ∀ t : ℝ, 0 ≤ t → t / Real.sqrt 2 ≤ t := fun t ht => div_le_self ht hs2
  have hβ0 : 0 ≤ β := by
    have h1 := hB.2.1 b 0 (Nat.zero_le _)
    have hq : 0 < (((ell : ℝ) ^ 0 * η)⁻¹ ^ 1) := by positivity
    rw [hf] at h1
    by_contra hneg; push Not at hneg
    nlinarith [frobNorm_nonneg (A b)]
  have homJ : 0 < omJ S ell k b := by unfold omJ; positivity
  refine (hdiv _ (frobNorm_nonneg _)).trans ?_
  by_cases hbs : bstrat S k b ≤ 1
  · -- crude case
    have hF : ∀ ν y, ν ≠ b.2 → frobNorm (FnuMu V ν b.2 y) ≤ 2 * β + 6 * β ^ 2 + 1024 * β ^ 3 := by
      intro ν y hν
      have := FnuMu_crude hη hell1 hrep hB hsm' ν b.2 hν y
      rwa [hf] at this
    have hc := JfieldLoc_crude (plaqIn (S.Om 0)) V b.1 b.2 _ hF
    have hb4 : β ≤ 1 / 4 := by linarith
    have a2 : β ^ 2 ≤ β * (1 / 4) := by nlinarith
    have a3 : β ^ 3 ≤ β * (1 / 16) := by nlinarith [pow_le_pow_left₀ hβ0 hb4 2]
    have hcr : 2 * (2 * (2 * β + 6 * β ^ 2 + 1024 * β ^ 3)) ≤ 270 * β := by nlinarith
    have hom : 1 ≤ (ell : ℝ) ^ 3 * omJ S ell k b := by
      unfold omJ
      have hp : (ell : ℝ) ^ bstrat S k b ≤ (ell : ℝ) ^ 1 := pow_le_pow_right₀ hellr hbs
      have hpos : (0 : ℝ) < (ell : ℝ) ^ bstrat S k b := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hpos.le (hp.trans_eq (pow_one _)) 3
    calc frobNorm (AdalyFormal.IngredientFamily.JfieldLoc (plaqIn (S.Om 0)) V b.1 b.2) ≤ 270 * β := hc.trans hcr
      _ ≤ 400 * β * ((ell : ℝ) ^ 3 * omJ S ell k b) := by nlinarith
      _ = 400 * (ell : ℝ) ^ 3 * β * omJ S ell k b := by ring
  · -- deep case: `bstrat b ≥ 2`
    push Not at hbs
    set x := b.1 with hx
    set μ := b.2 with hμ
    have hsx : bstrat S k b ≤ strat S k x := min_le_left _ _
    have hnear : ∀ z, pdist x z ≤ 4 → bstrat S k b ≤ strat S k z + 1 := fun z hz =>
      le_trans hsx (strat_le_near hA hell1 (hz.trans hRM))
    have hzin : ∀ z, pdist x z ≤ 3 → z ∈ S.Om 0 := fun z hz =>
      mem_om0_of_strat hA (by have := hnear z (by omega); omega)
    rw [JfieldLoc_eq_of_near (S.Om 0) V x μ hzin]
    set j : ℕ := bstrat S k b - 1 with hj
    have hj1 : j + 1 = bstrat S k b := by omega
    have hl := locRep_of_M1 hη hell1 hrep hB j hsm'
    -- every bond within distance 4 has `bstrat ≥ j`
    have hbond : ∀ e : Bond (scaleUp ell k Lu), pdist x e.1 ≤ 3 → j ≤ bstrat S k e := by
      intro e he
      have h2 := pd_sh he e.2
      have := bstrat_ge_near hA hell1 e (he.trans (by omega)) (h2.trans (by omega))
      omega
    have x0 : pdist x x ≤ 0 := pd0 x
    have hneed : ∀ ν, ν ≠ μ → NeedBonds (fun e => j ≤ bstrat S k e) (periodicLatticeShiftBack x ν) ν μ := by
      intro ν _
      have y1 := pd_bk x0 ν
      refine ⟨hbond _ (y1.trans (by norm_num)), hbond _ ((pd_sh y1 _).trans (by norm_num)),
        hbond _ ((pd_sh y1 _).trans (by norm_num)), hbond _ (y1.trans (by norm_num)),
        hbond _ ((pd_sh y1 _).trans (by norm_num)), hbond _ ((pd_sh (pd_sh y1 _) _).trans (by norm_num)),
        hbond _ ((pd_sh (pd_sh y1 _) _).trans (by norm_num))⟩
    have hdd : frobNorm (ddA η A x μ) ≤ (((12 : ℕ) : ℝ) * M * α₀) * (((ell : ℝ) ^ j * η)⁻¹ ^ 3) := by
      refine (hB.2.2.2 μ x j (fun ν _ => ?_)).le
      have y1 := pd_bk x0 ν
      refine ⟨⟨hbond _ ((pd_sh y1 _).trans (by norm_num)), hbond _ (y1.trans (by norm_num)),
        hbond _ ((pd_sh y1 _).trans (by norm_num)), hbond _ (y1.trans (by norm_num))⟩,
        ⟨hbond _ ((pd_sh x0 _).trans (by norm_num)), hbond _ (x0.trans (by norm_num)),
        hbond _ ((pd_sh x0 _).trans (by norm_num)), hbond _ (x0.trans (by norm_num))⟩⟩
    have hJ := hl.J_local_bound x μ _ hneed hdd
    rw [hf] at hJ
    -- the algebra: `η q = ℓ^{-j}`
    set t : ℝ := ((ell : ℝ) ^ j)⁻¹ with ht
    have hpj : (1 : ℝ) ≤ (ell : ℝ) ^ j := one_le_pow₀ hellr
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hpj
    set q : ℝ := ((ell : ℝ) ^ j * η)⁻¹ with hq
    have hηq : η * q = t := by
      rw [hq, ht, mul_inv, mul_comm ((ell : ℝ) ^ j)⁻¹, ← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul]
    have hpoly : η ^ 3 * (β * q ^ 3 + 40 * (β * q ^ 1) * (β * q ^ 2) + 4144 * (β * q ^ 1) ^ 3
        + 8192 * η * (β * q ^ 1) ^ 4) ≤ t ^ 3 * (β + 40 * β ^ 2 + 4144 * β ^ 3 + 8192 * β ^ 4) := by
      have e1 : η ^ 3 * (β * q ^ 3 + 40 * (β * q ^ 1) * (β * q ^ 2) + 4144 * (β * q ^ 1) ^ 3
          + 8192 * η * (β * q ^ 1) ^ 4)
          = (η * q) ^ 3 * (β + 40 * β ^ 2 + 4144 * β ^ 3) + 8192 * β ^ 4 * (η * q) ^ 4 := by ring
      rw [e1, hηq]
      have : t ^ 4 ≤ t ^ 3 := by
        have := pow_le_pow_left₀ ht0.le ht1 3
        nlinarith [pow_pos ht0 3]
      nlinarith [pow_nonneg hβ0 4]
    have hjp := jpoly_le β hβ0 hsm
    have hom : t ^ 3 = (ell : ℝ) ^ 3 * omJ S ell k b := by
      unfold omJ
      rw [← hj1, ht]
      have hpos : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
      field_simp
      ring
    calc frobNorm (Jfield V x μ) ≤ t ^ 3 * (β + 40 * β ^ 2 + 4144 * β ^ 3 + 8192 * β ^ 4) := hJ.trans hpoly
      _ ≤ t ^ 3 * (398 * β) := mul_le_mul_of_nonneg_left hjp (by positivity)
      _ ≤ t ^ 3 * (400 * β) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 400 * (ell : ℝ) ^ 3 * β * omJ S ell k b := by rw [hom]; ring

#print axioms pd_sh
#print axioms pd_bk
#print axioms pd0
#print axioms strat_le_near
#print axioms bstrat_ge_near
#print axioms mem_om0_of_strat
#print axioms FnuMuLoc_le
#print axioms FnuMuLoc_eq
#print axioms plaq_mem_of_near
#print axioms JfieldLoc_eq_of_near
#print axioms frob_conjByAmbient
#print axioms JfieldLoc_crude
#print axioms locRep_of_M1
#print axioms FnuMu_crude
#print axioms jpoly_le
#print axioms Jf_strat

end AdalyFormal.M1DStrat
