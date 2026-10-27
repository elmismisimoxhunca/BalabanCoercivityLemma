import M1B

/-!
# M2B1 -- the region-local M1 regime `M1RegularOn` and "class cube => `M1RegularOn` (cube)"  (m2_bridge_20261014, Layer B)

* `M1BoundsOn R S ell M f k α₀ η A` : the four clauses of lane B's `M1Bounds`, each demanded only where every bond it reads is a `CubeBond R`
  (both endpoints in the region `R`).  `M1RegularOn R ... U` : `∃ g A`, `U^g = exp(iηA)` on `CubeBond R`, and `M1BoundsOn R`.
* `m1RegularOn_univ_iff` : with `R = univ` this IS `M1Regular` (the local regime restricts to the global one, nothing lost).
* `M1RegularOn.mono`, `m1RegularOn_of_global` : restriction.
* `m1RegularOn_of_class` : on a CLASS CUBE of index `j` (`IsClassCube`), the printed per-cube class `PerCubeRegular2` at `α₀` gives
  `M1RegularOn cube` at `ell^3 * α₀`.  Reason (`bstrat_le_succ_of_cubeBond`): every bond of a class cube has both-endpoint stratum in
  `{j, j+1}`, so the stratum-weighted M1 bound (`j' <= bstrat <= j+1`) is the class bound with scale `ell^(j+1)` in place of `ell^j`,
  i.e. weaker than the class bound by a factor `ell^p <= ell^3` for the clause of order `p`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.M1 (M1Bounds M1Regular StratReads bstrat strat strat_eq_iff le_bstrat_of_cubeBond classCube_sub)

variable {L : PeriodicLatticeExtent}

/-- the M1 bounds on a field `A`, demanded only where every bond read lies in the region `R`. -/
def M1BoundsOn (R : Set (PeriodicLatticeSite L)) (S : Tower L) (ell M f k : ℕ) (α₀ η : ℝ)
    (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ e : Bond L, CubeBond R e → HT (A e)) ∧
  (∀ (e : Bond L) (j : ℕ), CubeBond R e → j ≤ bstrat S k e →
      frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
  (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      CubeBond R ((x, ν) : Bond L) → CubeBond R ((periodicLatticeShift x μ, ν) : Bond L) →
      j ≤ bstrat S k (x, ν) → j ≤ bstrat S k (periodicLatticeShift x μ, ν) →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
        < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
  (∀ (μ : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      (∀ ν : Fin 3, ν ≠ μ → CurlReads R (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads R x ν μ) →
      (∀ ν : Fin 3, ν ≠ μ → StratReads S k j (periodicLatticeShiftBack x ν) ν μ ∧ StratReads S k j x ν μ) →
      frobNorm (ddA η A x μ) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

/-- **the region-local M1 regime**: a gauge `g` and a field `A` with `U^g = exp(iηA)` on the bonds of `R` and `M1BoundsOn R`. -/
def M1RegularOn (R : Set (PeriodicLatticeSite L)) (ell M f k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ e : Bond L, CubeBond R e →
      ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
    M1BoundsOn R S ell M f k α₀ η A

theorem cubeBond_univ (e : Bond L) : CubeBond (Set.univ : Set (PeriodicLatticeSite L)) e := ⟨trivial, trivial⟩

theorem curlReads_univ (x : PeriodicLatticeSite L) (a b : Fin 3) :
    CurlReads (Set.univ : Set (PeriodicLatticeSite L)) x a b := ⟨cubeBond_univ _, cubeBond_univ _, cubeBond_univ _, cubeBond_univ _⟩

/-- with `R = univ` the local regime is lane B's `M1Regular`. -/
theorem m1RegularOn_univ_iff {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    M1RegularOn Set.univ ell M f k S α₀ η U ↔ M1Regular ell M f k S α₀ η U := by
  constructor
  · rintro ⟨g, A, hU, hHT, h1, h2, h3⟩
    refine ⟨g, A, fun e => hU e (cubeBond_univ e), fun e => hHT e (cubeBond_univ e), ?_, ?_, ?_⟩
    · exact fun e j hj => h1 e j (cubeBond_univ e) hj
    · exact fun μ ν x j h1' h2' => h2 μ ν x j (cubeBond_univ _) (cubeBond_univ _) h1' h2'
    · exact fun μ x j hr => h3 μ x j (fun ν _ => ⟨curlReads_univ _ _ _, curlReads_univ _ _ _⟩) hr
  · rintro ⟨g, A, hU, hHT, h1, h2, h3⟩
    refine ⟨g, A, fun e _ => hU e, fun e _ => hHT e, ?_, ?_, ?_⟩
    · exact fun e j _ hj => h1 e j hj
    · exact fun μ ν x j _ _ h1' h2' => h2 μ ν x j h1' h2'
    · exact fun μ x j _ hr => h3 μ x j hr

theorem cubeBond_mono {R R' : Set (PeriodicLatticeSite L)} (h : R ⊆ R') {e : Bond L} (he : CubeBond R e) : CubeBond R' e :=
  ⟨h he.1, h he.2⟩

theorem curlReads_mono {R R' : Set (PeriodicLatticeSite L)} (h : R ⊆ R') {x : PeriodicLatticeSite L} {a b : Fin 3}
    (hr : CurlReads R x a b) : CurlReads R' x a b :=
  ⟨cubeBond_mono h hr.1, cubeBond_mono h hr.2.1, cubeBond_mono h hr.2.2.1, cubeBond_mono h hr.2.2.2⟩

/-- restriction to a smaller region. -/
theorem M1RegularOn.mono {R R' : Set (PeriodicLatticeSite L)} (h : R ⊆ R') {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ}
    {U : LinkCfg L} (hU : M1RegularOn R' ell M f k S α₀ η U) : M1RegularOn R ell M f k S α₀ η U := by
  obtain ⟨g, A, hg, hHT, h1, h2, h3⟩ := hU
  refine ⟨g, A, fun e he => hg e (cubeBond_mono h he), fun e he => hHT e (cubeBond_mono h he), ?_, ?_, ?_⟩
  · exact fun e j he hj => h1 e j (cubeBond_mono h he) hj
  · exact fun μ ν x j a b c d => h2 μ ν x j (cubeBond_mono h a) (cubeBond_mono h b) c d
  · exact fun μ x j hr hs => h3 μ x j (fun ν hν => ⟨curlReads_mono h (hr ν hν).1, curlReads_mono h (hr ν hν).2⟩) hs

/-- the global regime gives the local one on every region. -/
theorem m1RegularOn_of_global {R : Set (PeriodicLatticeSite L)} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hU : M1Regular ell M f k S α₀ η U) : M1RegularOn R ell M f k S α₀ η U :=
  (m1RegularOn_univ_iff.mpr hU).mono (Set.subset_univ _)

/-! ## class cube => local M1 regime -/

/-- every bond of a class cube of index `j` has both-endpoint stratum `≤ j + 1` (and `≥ j`, `le_bstrat_of_cubeBond`). -/
theorem strat_le_succ_of_mem {ell M R f k : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M f k S sites j)
    {x : PeriodicLatticeSite L} (hx : x ∈ sites) : strat S k x ≤ j + 1 := by
  have hjk : j ≤ k := hq.1.1
  rcases hq.1.2.2.1 hx with h | h
  · have := ((strat_eq_iff hA hjk x).mp h).2
    omega
  · by_cases hk : j + 1 ≤ k
    · have := ((strat_eq_iff hA hk x).mp h).2
      omega
    · exfalso
      have : S.Om (j + 1) = ∅ := hA.2.1 (j + 1) (by omega)
      have h1 := h.1
      rw [this] at h1
      exact h1

theorem bstrat_le_succ_of_cubeBond {ell M R f k : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M f k S sites j) {e : Bond L}
    (he : CubeBond sites e) : bstrat S k e ≤ j + 1 :=
  le_trans (min_le_left _ _) (strat_le_succ_of_mem hA hq he.1)

/-- the scale comparison: `(ell^j η)⁻¹^p ≤ ell^3 (ell^j' η)⁻¹^p` for `j' ≤ j+1`, `p ≤ 3`. -/
theorem scale_cmp {ell : ℕ} (hell : 1 ≤ ell) {η : ℝ} (hη : 0 < η) {j j' : ℕ} (h : j' ≤ j + 1) {p : ℕ} (hp : p ≤ 3) :
    (((ell : ℝ) ^ j * η)⁻¹) ^ p ≤ (ell : ℝ) ^ 3 * (((ell : ℝ) ^ j' * η)⁻¹) ^ p := by
  have hell' : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl0 : (0 : ℝ) < ell := by linarith
  set a := ((ell : ℝ) ^ j * η)⁻¹ with ha
  set b := ((ell : ℝ) ^ j' * η)⁻¹ with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hab : a ≤ ell * b := by
    rw [ha, hb]
    have hpow : (ell : ℝ) ^ j' ≤ (ell : ℝ) ^ (j + 1) := pow_le_pow_right₀ hell' h
    have h1 : ((ell : ℝ) ^ j * η)⁻¹ = (ell : ℝ) * (((ell : ℝ) ^ (j + 1)) * η)⁻¹ := by
      rw [pow_succ]; field_simp
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hl0.le
    apply inv_anti₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hpow hη.le
  have h1 : a ^ p ≤ ((ell : ℝ) * b) ^ p := pow_le_pow_left₀ ha0.le hab p
  have h2 : ((ell : ℝ) * b) ^ p = (ell : ℝ) ^ p * b ^ p := mul_pow _ _ _
  have h3 : (ell : ℝ) ^ p ≤ (ell : ℝ) ^ 3 := pow_le_pow_right₀ hell' hp
  calc a ^ p ≤ ((ell : ℝ) * b) ^ p := h1
    _ = (ell : ℝ) ^ p * b ^ p := h2
    _ ≤ (ell : ℝ) ^ 3 * b ^ p := mul_le_mul_of_nonneg_right h3 (by positivity)

theorem bound_transfer {ell : ℕ} (hell : 1 ≤ ell) {η : ℝ} (hη : 0 < η) {j j' : ℕ} (h : j' ≤ j + 1) {p : ℕ} (hp : p ≤ 3)
    {f M : ℕ} {α₀ : ℝ} (hα : 0 ≤ α₀) {x : ℝ}
    (hx : x < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p)) :
    x < (f : ℝ) * M * ((ell : ℝ) ^ 3 * α₀) * (((ell : ℝ) ^ j' * η)⁻¹ ^ p) := by
  refine lt_of_lt_of_le hx ?_
  have hc : 0 ≤ (f : ℝ) * M * α₀ := by positivity
  have := mul_le_mul_of_nonneg_left (scale_cmp hell hη h hp) hc
  calc (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p)
      ≤ (f : ℝ) * M * α₀ * ((ell : ℝ) ^ 3 * (((ell : ℝ) ^ j' * η)⁻¹ ^ p)) := this
    _ = (f : ℝ) * M * ((ell : ℝ) ^ 3 * α₀) * (((ell : ℝ) ^ j' * η)⁻¹ ^ p) := by ring

/-- **the printed class cube gives the local M1 regime** (`α₀ ↦ ell^3 α₀`): on a class cube of index `j`, `PerCubeRegular2` implies
`M1RegularOn cube`.  The constant `ell^3` is the worst stratum jump (`j → j+1`) over the order-3 clause. -/
theorem m1RegularOn_of_class {ell M R f k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hell : 1 ≤ ell) {α₀ η : ℝ}
    (hα : 0 ≤ α₀) (hη : 0 < η) {U : LinkCfg L} (hP : PerCubeRegular2 ell M f k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M f k S sites j) :
    M1RegularOn sites ell M f k S ((ell : ℝ) ^ 3 * α₀) η U := by
  obtain ⟨g, A, hc1, hc2, hc3⟩ := hP sites j hq
  have hb := fun e (he : CubeBond sites e) => bstrat_le_succ_of_cubeBond hA hq he
  refine ⟨g, A, fun e he => (hc1 e he).2.1, fun e he => (hc1 e he).1, ?_, ?_, ?_⟩
  · intro e j' he hj'
    exact bound_transfer hell hη (hb e he |>.trans' hj') (by norm_num) hα (hc1 e he).2.2
  · intro μ ν x j' h1 h2 hj1 hj2
    exact bound_transfer hell hη (hb _ h1 |>.trans' hj1) (by norm_num) hα (hc2 μ ν x h1 h2)
  · intro μ x j' hr hs
    obtain ⟨ν, hν⟩ : ∃ ν : Fin 3, ν ≠ μ := by
      fin_cases μ
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    have hj' : j' ≤ j + 1 := (hb _ (hr ν hν).2.1).trans' (hs ν hν).2.1
    exact bound_transfer hell hη hj' (by norm_num) hα (hc3 μ x hr)

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.m1RegularOn_univ_iff
#print axioms AdalyFormal.M2Bridge.M1RegularOn.mono
#print axioms AdalyFormal.M2Bridge.m1RegularOn_of_global
#print axioms AdalyFormal.M2Bridge.bstrat_le_succ_of_cubeBond
#print axioms AdalyFormal.M2Bridge.scale_cmp
#print axioms AdalyFormal.M2Bridge.m1RegularOn_of_class
