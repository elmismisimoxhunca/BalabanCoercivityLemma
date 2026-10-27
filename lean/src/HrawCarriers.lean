/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import MechG16
import AdalyFormal.Balaban.CoarseCurl
import AdalyFormal.Balaban.RegularUPerturbation
import AdalyFormal.Balaban.RegularUDomainWitness

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# THE TWO CARRIER OBJECTS `compute/terminal_assembly/SCOPE.md` §3b NAMES AS MISSING

Nothing here is graded by this lane (BUILD DISCIPLINE 8): it reports facts.
-/

namespace AdalyFormal.HrawCarriers

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette coarseShift coarseShift_val_eq
  coarseShift_apply_ne coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant)
open AdalyFormal.Balaban.ThirdLevelStokes (coarseCurlSuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU PlaqFnL2)
open AdalyFormal.Balaban.BridgeInverse (CoarseFnL2 qCLM)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg curlDrift plaqEnergy
  bondEnergy norm_curlDrift_L2_le_sup)
open AdalyFormal.Balaban.RegularUDomainWitness (frobSupBond_trivialU)
open AdalyFormal.MechEdges.G16 (CoarsePlaqFnL2 coarseCurlCLM_L2 coarseCurlCLM_L2_apply hraw_op
  rawSigmaZero rawErrorCoeff rawErrorCoeff_nonneg rawSigmaZero_pos pilp_norm_eq_sqrt_sum
  norm_bondFnL2)

variable {L L' : PeriodicLatticeExtent}

/-! ## §1 — THE SCALE RELATION -/

/-- **`L'` is the extent of the torus at scale `ell` under `L`**: side length `L μ + 1` splits into
exactly `L' μ + 1` blocks of `ell` fine sites.  Stated as the EQUATION `ell·(L' μ + 1) = L μ + 1`
rather than as `L' μ + 1 = (L μ + 1)/ell`, so that no truncating `Nat` division appears in the
hypothesis and the divisibility `ell ∣ (L μ + 1)` is a CONSEQUENCE (`dvd_of_scale`), not a separate
assumption that could drift out of sync. -/
def ScaleQuotient (L : PeriodicLatticeExtent) (ell : ℕ) (L' : PeriodicLatticeExtent) : Prop :=
  ∀ μ : Fin 3, ell * (L' μ + 1) = L μ + 1

/-- `0 < ell` from the scale relation alone: `ell = 0` would force `L μ + 1 = 0`. -/
theorem ell_pos_of_scale {ell : ℕ} (h : ScaleQuotient L ell L') : 0 < ell := by
  rcases Nat.eq_zero_or_pos ell with hz | hp
  · exfalso
    have := h 0
    rw [hz] at this
    omega
  · exact hp

/-- **The tiling hypothesis is IMPLIED**, not assumed alongside. -/
theorem dvd_of_scale {ell : ℕ} (h : ScaleQuotient L ell L') (μ : Fin 3) : ell ∣ (L μ + 1) :=
  ⟨L' μ + 1, (h μ).symm⟩

/-! ## §2 — THE SITE EQUIVALENCE `Λ' ≃ sites of L'` -/

/-- `y ↦ y/ell`, coordinatewise. -/
def coarseSiteFwd {ell : ℕ} (h : ScaleQuotient L ell L')
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) : PeriodicLatticeSite L' :=
  fun μ => ⟨(y.1 μ).val / ell, by
    have hell := ell_pos_of_scale h
    have hlt : (y.1 μ).val < ell * (L' μ + 1) := by rw [h μ]; exact (y.1 μ).isLt
    exact (Nat.div_lt_iff_lt_mul hell).mpr (by rw [Nat.mul_comm]; exact hlt)⟩

/-- `z ↦ ell·z`, coordinatewise, landing in the coarse-centre lattice. -/
def coarseSiteBwd {ell : ℕ} (h : ScaleQuotient L ell L') (z : PeriodicLatticeSite L') :
    {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} :=
  ⟨fun μ => ⟨ell * (z μ).val, by
      have hlt : ell * (z μ).val < ell * (L' μ + 1) :=
        mul_lt_mul_of_pos_left (z μ).isLt (ell_pos_of_scale h)
      rw [h μ] at hlt; exact hlt⟩,
   mem_CoarseLattice.mpr (fun μ => by
      show (ell * (z μ).val) % ell = 0
      exact Nat.mul_mod_right ell _)⟩

/-- **OBJECT 1a — THE SITE HALF OF THE EXTENT IDENTIFICATION.** -/
def coarseSiteEquiv {ell : ℕ} (h : ScaleQuotient L ell L') :
    {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell} ≃ PeriodicLatticeSite L' where
  toFun := coarseSiteFwd h
  invFun := coarseSiteBwd h
  left_inv := by
    intro y
    apply Subtype.ext
    funext μ
    apply Fin.ext
    show ell * ((y.1 μ).val / ell) = (y.1 μ).val
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp y.2 μ))
  right_inv := by
    intro z
    funext μ
    apply Fin.ext
    show (ell * (z μ).val) / ell = (z μ).val
    exact Nat.mul_div_cancel_left _ (ell_pos_of_scale h)

theorem coarseSiteEquiv_val {ell : ℕ} (h : ScaleQuotient L ell L')
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) (μ : Fin 3) :
    ((coarseSiteEquiv h y) μ).val = (y.1 μ).val / ell := rfl

theorem coarseSiteEquiv_symm_val {ell : ℕ} (h : ScaleQuotient L ell L')
    (z : PeriodicLatticeSite L') (μ : Fin 3) :
    (((coarseSiteEquiv h).symm z).1 μ).val = ell * (z μ).val := rfl

/-- The `μ`-component of a single fine shift on `L'`, in `Nat` form. -/
theorem shift_val_eq (z : PeriodicLatticeSite L') (μ : Fin 3) :
    ((periodicLatticeShift z μ) μ).val = ((z μ).val + 1) % (L' μ + 1) := by
  rw [AdalyFormal.Balaban.CoarseCurl.periodicLatticeShift_self, Fin.val_add, Fin.val_one',
    Nat.add_mod_mod]

/-- **THE GEOMETRIC HEART OF OBJECT 1**: the coarse lattice's own adjacency (`coarseShift`, an
`ell`-fold fine step) becomes the ORDINARY unit step on `L'` under the identification.  This is what
makes the identification an identification of LATTICES and not merely of index sets. -/
theorem coarseSiteEquiv_coarseShift {ell : ℕ} (h : ScaleQuotient L ell L')
    (y : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) (μ : Fin 3) :
    coarseSiteEquiv h ⟨coarseShift y.1 ell μ,
        coarseShift_mem_coarseLattice (dvd_of_scale h) y.2 μ⟩
      = periodicLatticeShift (coarseSiteEquiv h y) μ := by
  have hell := ell_pos_of_scale h
  funext ν
  apply Fin.ext
  by_cases hν : ν = μ
  · subst hν
    rw [coarseSiteEquiv_val, shift_val_eq, coarseSiteEquiv_val]
    show (coarseShift y.1 ell ν ν).val / ell = _
    rw [coarseShift_val_eq]
    -- write the coarse coordinate as `ell * k` and the extent as `ell * m`
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp y.2 ν)
    have hm : L ν + 1 = ell * (L' ν + 1) := (h ν).symm
    rw [hk, hm, ← Nat.mul_succ, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hell,
      Nat.mul_div_cancel_left _ hell]
  · rw [coarseSiteEquiv_val]
    show (coarseShift y.1 ell μ ν).val / ell = _
    rw [coarseShift_apply_ne y.1 ell μ ν hν]
    show (y.1 ν).val / ell = ((periodicLatticeShift (coarseSiteEquiv h y) μ) ν).val
    rw [periodicLatticeShift, Function.update_of_ne hν, coarseSiteEquiv_val]

/-! ## §3 — THE BOND AND PLAQUETTE EQUIVALENCES, AND THE `ℓ²` ISOMETRY -/

/-- **OBJECT 1 — `CoarseBond L ell ≃ Bond L'`.** -/
def coarseBondEquiv {ell : ℕ} (h : ScaleQuotient L ell L') : CoarseBond L ell ≃ Bond L' :=
  (coarseSiteEquiv h).prodCongr (Equiv.refl (Fin 3))

/-- The plaquette analogue, needed for the target side of the curl. -/
def coarsePlaqEquiv {ell : ℕ} (h : ScaleQuotient L ell L') :
    CoarsePlaquette L ell ≃ PeriodicLatticePlaquette L' :=
  (coarseSiteEquiv h).prodCongr (Equiv.refl PeriodicPlaquetteDirections)

theorem coarseBondEquiv_apply {ell : ℕ} (h : ScaleQuotient L ell L') (b : CoarseBond L ell) :
    coarseBondEquiv h b = (coarseSiteEquiv h b.1, b.2) := rfl

theorem coarsePlaqEquiv_apply {ell : ℕ} (h : ScaleQuotient L ell L') (p : CoarsePlaquette L ell) :
    coarsePlaqEquiv h p = (coarseSiteEquiv h p.1, p.2) := rfl

/-- **THE `ℓ²` STRUCTURE TRANSPORTS ISOMETRICALLY.**  Both carriers are `PiLp 2` over the SAME
fibre `𝔰𝔲(2)` — the fibre is not changed, only the index set — so `piLpCongrLeft` (Mathlib, REUSED)
delivers a `LinearIsometryEquiv` outright.  §3a below states the two consequences (norms, inner
products) as named theorems so no consumer has to unfold this definition. -/
noncomputable def coarseFnL2Equiv {ell : ℕ} (h : ScaleQuotient L ell L') :
    CoarseFnL2 L ell ≃ₗᵢ[ℝ] BondFnL2 L' :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (coarseBondEquiv h)

/-- The plaquette-side isometry, same construction. -/
noncomputable def coarsePlaqFnL2Equiv {ell : ℕ} (h : ScaleQuotient L ell L') :
    AdalyFormal.MechEdges.G16.CoarsePlaqFnL2 L ell ≃ₗᵢ[ℝ] PlaqFnL2 L' :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (coarsePlaqEquiv h)

/-! ### §3a — the two structure facts, named -/

/-- **THE NORMS AGREE** (S83/`carrier-is-scalar` guard: this is the statement that the
identification is an identification of HILBERT SPACES, not of index sets). -/
theorem norm_coarseFnL2Equiv {ell : ℕ} (h : ScaleQuotient L ell L') (B : CoarseFnL2 L ell) :
    ‖coarseFnL2Equiv h B‖ = ‖B‖ := (coarseFnL2Equiv h).norm_map B

/-- **THE INNER PRODUCTS AGREE.** -/
theorem inner_coarseFnL2Equiv {ell : ℕ} (h : ScaleQuotient L ell L') (B C : CoarseFnL2 L ell) :
    (inner ℝ (coarseFnL2Equiv h B) (coarseFnL2Equiv h C) : ℝ) = inner ℝ B C :=
  (coarseFnL2Equiv h).inner_map_map B C

theorem norm_coarsePlaqFnL2Equiv {ell : ℕ} (h : ScaleQuotient L ell L')
    (F : AdalyFormal.MechEdges.G16.CoarsePlaqFnL2 L ell) :
    ‖coarsePlaqFnL2Equiv h F‖ = ‖F‖ := (coarsePlaqFnL2Equiv h).norm_map F

/-- The pointwise value of the transported field: `(e B)(b') = B(e⁻¹ b')`. -/
theorem coarseFnL2Equiv_apply {ell : ℕ} (h : ScaleQuotient L ell L') (B : CoarseFnL2 L ell)
    (b : Bond L') :
    WithLp.ofLp (coarseFnL2Equiv h B) b = WithLp.ofLp B ((coarseBondEquiv h).symm b) := rfl

theorem coarsePlaqFnL2Equiv_apply {ell : ℕ} (h : ScaleQuotient L ell L')
    (F : AdalyFormal.MechEdges.G16.CoarsePlaqFnL2 L ell) (p : PeriodicLatticePlaquette L') :
    WithLp.ofLp (coarsePlaqFnL2Equiv h F) p = WithLp.ofLp F ((coarsePlaqEquiv h).symm p) := rfl

/-! ## §4 — THE INTERTWINING: THE COARSE CURL **IS** THE UNIT-SCALE CURL ON `L'` -/

/-- The `symm` of the bond equivalence, componentwise (`rfl`, stated so proofs never unfold it). -/
theorem coarseBondEquiv_symm_apply {ell : ℕ} (h : ScaleQuotient L ell L')
    (z : PeriodicLatticeSite L') (ρ : Fin 3) :
    (coarseBondEquiv h).symm (z, ρ) = ((coarseSiteEquiv h).symm z, ρ) := rfl

/-- **OBJECT 1, THE INTERTWINING HALF.**  `∂₁'` at `(L, ell)`, read through the identification, IS
the ordinary unit-scale curl at the trivial background on `L'`:

    coarseCurlSuTwo hdvd B p  =  curlValueCovariant 1 (B ∘ e⁻¹) (ê p) .

This is the statement `compute/terminal_assembly/SCOPE.md` §3b's row (1) needs: the coarse map at
`(L, ell)` followed by the identification equals the identity-scale reading on `L'`. -/
theorem coarseCurlSuTwo_transport {ell : ℕ} (h : ScaleQuotient L ell L')
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseBond L ell → SuTwo)
    (p : CoarsePlaquette L ell) :
    coarseCurlSuTwo hdvd B p
      = curlValueCovariant (trivialU L') (fun b => B ((coarseBondEquiv h).symm b))
          (coarsePlaqEquiv h p) := by
  have hbase : (coarseSiteEquiv h).symm (coarseSiteEquiv h p.1) = p.1 :=
    (coarseSiteEquiv h).symm_apply_apply p.1
  have hshift : ∀ μ : Fin 3, (coarseSiteEquiv h).symm
      (periodicLatticeShift (coarseSiteEquiv h p.1) μ)
        = ⟨coarseShift p.1.1 ell μ, coarseShift_mem_coarseLattice hdvd p.1.2 μ⟩ := by
    intro μ
    rw [← coarseSiteEquiv_coarseShift h p.1 μ]
    exact (coarseSiteEquiv h).symm_apply_apply _
  show _ = curlValueCovariant (trivialU L') _ (coarseSiteEquiv h p.1, p.2)
  unfold curlValueCovariant coarseCurlSuTwo
  simp only [trivialU, RMap_one, LinearMap.id_coe, id_eq, coarseBondEquiv_symm_apply, hbase,
    hshift]

/-! ## §5 — OBJECT 2: THE COVARIANTISED COARSE CURL

`ThirdLevelStokes.coarseCurlSuTwo` takes NO background argument (it is the flat four-term
difference).  §5 gives it one: a link configuration on the COARSE bonds — Bałaban's blocked
background `Ū` at the next level — entering exactly as `curlValueCovariant` has it enter at the fine
level, by ADJOINT CONJUGATION on the two shifted terms (`RMap`), never as a sign flip. -/

/-- Link configurations on the coarse bond set — the level-`(j+1)` background, intrinsically on the
coarse lattice.  §5c shows it is the same thing as a `PeriodicLinkConfiguration` on `L'`. -/
abbrev CoarseLinkConfiguration (L : PeriodicLatticeExtent) (ell : ℕ) : Type :=
  CoarseBond L ell → Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- **OBJECT 2 — `∂₁'(Ū)`, the coarse curl at a coarse background.**  Term for term
`CovariantOperators.curlValueCovariant` with `coarseShift` in place of `periodicLatticeShift`, i.e.
`ThirdLevelStokes.coarseCurlSuTwo` with the two shifted terms conjugated by the background. -/
noncomputable def coarseCurlSuTwoCov {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : CoarseLinkConfiguration L ell) (B : CoarseBond L ell → SuTwo)
    (p : CoarsePlaquette L ell) : SuTwo :=
  B (p.1, p.2.1.1)
    + RMap (V (p.1, p.2.1.1))
        (B (⟨coarseShift p.1.1 ell p.2.1.1,
          coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.1⟩, p.2.1.2))
    - RMap (V (p.1, p.2.1.2))
        (B (⟨coarseShift p.1.1 ell p.2.1.2,
          coarseShift_mem_coarseLattice hdvd p.1.2 p.2.1.2⟩, p.2.1.1))
    - B (p.1, p.2.1.2)

/-- The trivial coarse background. -/
def trivialCoarseU (L : PeriodicLatticeExtent) (ell : ℕ) : CoarseLinkConfiguration L ell :=
  fun _ => 1

/-- **REDUCTION TO THE FLAT COARSE CURL AT `Ū = 1` — A THEOREM, NOT A REMARK.** -/
theorem coarseCurlSuTwoCov_trivial {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlSuTwoCov hdvd (trivialCoarseU L ell) B p = coarseCurlSuTwo hdvd B p := by
  unfold coarseCurlSuTwoCov coarseCurlSuTwo trivialCoarseU
  simp only [RMap_one, LinearMap.id_coe, id_eq]

/-- **OBJECT 2 IS THE COVARIANT CURL ONE LEVEL UP.**  Under the extent identification, the
covariantised coarse curl at coarse background `V` IS `curlValueCovariant` at the transported
background on `L'`.  Together with §4 this is the whole content of "the coarse plaquette holonomy at
the coarse configuration". -/
theorem coarseCurlSuTwoCov_transport {ell : ℕ} (h : ScaleQuotient L ell L')
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (V : CoarseLinkConfiguration L ell)
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlSuTwoCov hdvd V B p
      = curlValueCovariant (fun b => V ((coarseBondEquiv h).symm b))
          (fun b => B ((coarseBondEquiv h).symm b)) (coarsePlaqEquiv h p) := by
  have hbase : (coarseSiteEquiv h).symm (coarseSiteEquiv h p.1) = p.1 :=
    (coarseSiteEquiv h).symm_apply_apply p.1
  have hshift : ∀ μ : Fin 3, (coarseSiteEquiv h).symm
      (periodicLatticeShift (coarseSiteEquiv h p.1) μ)
        = ⟨coarseShift p.1.1 ell μ, coarseShift_mem_coarseLattice hdvd p.1.2 μ⟩ := by
    intro μ
    rw [← coarseSiteEquiv_coarseShift h p.1 μ]
    exact (coarseSiteEquiv h).symm_apply_apply _
  show _ = curlValueCovariant _ _ (coarseSiteEquiv h p.1, p.2)
  unfold curlValueCovariant coarseCurlSuTwoCov
  simp only [coarseBondEquiv_symm_apply, hbase, hshift]

/-- **THE DRIFT, IDENTIFIED WITH THE FINE-LEVEL DRIFT ONE LEVEL UP.**  The difference between the
covariantised and the flat coarse curl IS `RegularUPerturbation.curlDrift` at `L'` — so the drift
estimate does not have to be re-proved, it is the tree's own `norm_curlDrift_L2_le` applied at the
coarse level (LAW-19). -/
theorem coarseCurlSuTwoCov_sub_flat {ell : ℕ} (h : ScaleQuotient L ell L')
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (V : CoarseLinkConfiguration L ell)
    (B : CoarseBond L ell → SuTwo) (p : CoarsePlaquette L ell) :
    coarseCurlSuTwoCov hdvd V B p - coarseCurlSuTwo hdvd B p
      = AdalyFormal.Balaban.RegularUPerturbation.curlDrift
          (fun b => V ((coarseBondEquiv h).symm b))
          (fun b => B ((coarseBondEquiv h).symm b)) (coarsePlaqEquiv h p) := by
  rw [coarseCurlSuTwoCov_transport h hdvd V B p, coarseCurlSuTwo_transport h hdvd B p]
  rfl

/-! ### §5a — the drift bound at the coarse level, with the SAME constant `4√2` -/

/-- **THE COARSE DRIFT BOUND.**  `√(∑_P ‖(∂₁'(Ū) − ∂₁')B(P)‖²) ≤ 4√2·α·√(∑_b ‖B(b)‖²)` for any
uniform bound `α` on `frobNorm(Ū(b) − 1)` over COARSE bonds.  Constant `4√2 = √32`, identical to the
fine-level one, because it IS the fine-level one read at `L'`. -/
theorem coarse_drift_energy_le {ell : ℕ} (h : ScaleQuotient L ell L')
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (V : CoarseLinkConfiguration L ell)
    (B : CoarseBond L ell → SuTwo) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : ∀ b : CoarseBond L ell,
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((V b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    Real.sqrt (∑ P : CoarsePlaquette L ell,
        ‖coarseCurlSuTwoCov hdvd V B P - coarseCurlSuTwo hdvd B P‖ ^ 2)
      ≤ 4 * Real.sqrt 2 * α * Real.sqrt (∑ b : CoarseBond L ell, ‖B b‖ ^ 2) := by
  set V' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L' :=
    fun b => V ((coarseBondEquiv h).symm b) with hV'
  set B' : Bond L' → SuTwo := fun b => B ((coarseBondEquiv h).symm b) with hB'
  have hplaq : (∑ P : CoarsePlaquette L ell,
      ‖coarseCurlSuTwoCov hdvd V B P - coarseCurlSuTwo hdvd B P‖ ^ 2)
      = AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
          (AdalyFormal.Balaban.RegularUPerturbation.curlDrift V' B') := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.plaqEnergy
    rw [← Equiv.sum_comp (coarsePlaqEquiv h)
      (fun p => ‖AdalyFormal.Balaban.RegularUPerturbation.curlDrift V' B' p‖ ^ 2)]
    exact Finset.sum_congr rfl (fun P _ => by
      rw [coarseCurlSuTwoCov_sub_flat h hdvd V B P])
  have hbond : (∑ b : CoarseBond L ell, ‖B b‖ ^ 2)
      = AdalyFormal.Balaban.RegularUPerturbation.bondEnergy B' := by
    unfold AdalyFormal.Balaban.RegularUPerturbation.bondEnergy
    rw [← Equiv.sum_comp (coarseBondEquiv h) (fun b => ‖B' b‖ ^ 2)]
    exact Finset.sum_congr rfl (fun b _ => by
      rw [hB']
      show ‖B b‖ ^ 2 = ‖B ((coarseBondEquiv h).symm (coarseBondEquiv h b))‖ ^ 2
      rw [(coarseBondEquiv h).symm_apply_apply])
  rw [hplaq, hbond]
  refine AdalyFormal.Balaban.RegularUPerturbation.norm_curlDrift_L2_le V' B' α hα0 ?_
  intro b
  exact hα ((coarseBondEquiv h).symm b)

/-! ## §6 — THE OPERATOR LEVEL: `∂₁'` AND `∂₁'(Ū)` AS CONTINUOUS LINEAR MAPS, AND THE TWO
IDENTITIES THAT CROSS THE CARRIER GAP -/

/-- `∂₁'(Ū)` as a bare `LinearMap` on the function types (the `RMap`s are linear, so both fields
come from `LinearMap.map_add`/`map_smul` at the fibre). -/
noncomputable def coarseCurlCovLM {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : CoarseLinkConfiguration L ell) :
    (CoarseBond L ell → SuTwo) →ₗ[ℝ] (CoarsePlaquette L ell → SuTwo) where
  toFun := coarseCurlSuTwoCov hdvd V
  map_add' B1 B2 := by
    funext p
    simp only [coarseCurlSuTwoCov, Pi.add_apply, map_add]
    abel
  map_smul' c B := by
    funext p
    simp only [coarseCurlSuTwoCov, Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, smul_sub]

/-- `∂₁'(Ū) : CoarseFnL2 L ell →L[ℝ] CoarsePlaqFnL2 L ell`, by `MechG16.coarseCurlCLM_L2`'s own
recipe (LAW-19). -/
noncomputable def coarseCurlCovCLM_L2 {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : CoarseLinkConfiguration L ell) :
    CoarseFnL2 L ell →L[ℝ] AdalyFormal.MechEdges.G16.CoarsePlaqFnL2 L ell :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (CoarsePlaquette L ell → SuTwo)).symm.toLinearMap.comp
      ((coarseCurlCovLM hdvd V).comp
        (WithLp.linearEquiv 2 ℝ (CoarseBond L ell → SuTwo)).toLinearMap))

theorem coarseCurlCovCLM_L2_apply {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : CoarseLinkConfiguration L ell) (B : CoarseFnL2 L ell) (p : CoarsePlaquette L ell) :
    WithLp.ofLp (coarseCurlCovCLM_L2 hdvd V B) p
      = coarseCurlSuTwoCov hdvd V (WithLp.ofLp B) p := rfl

/-- The `ofLp` reading of `curlCovariantCLM_L2`, needed on both sides of §6a. -/
theorem ofLp_curlCovariantCLM_L2
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (X : BondFnL2 L) (p : PeriodicLatticePlaquette L) :
    WithLp.ofLp (curlCovariantCLM_L2 U X) p = curlValueCovariant U (WithLp.ofLp X) p := by
  have h : curlCovariantCLM_L2 U (WithLp.toLp 2 (WithLp.ofLp X))
      = WithLp.toLp 2 (curlValueCovariant U (WithLp.ofLp X)) :=
    AdalyFormal.Balaban.DeltaKFull.curlCovariantCLM_L2_toLp U (WithLp.ofLp X)
  have hX : (WithLp.toLp 2 (WithLp.ofLp X) : BondFnL2 L) = X := rfl
  rw [hX] at h
  rw [h]

/-! ### §6a — THE TWO CROSSING IDENTITIES -/

/-- **THE FLAT COARSE CURL, CROSSED.**  `∂₁'` at `(L, ell)`, transported to `L'`, IS
`curlCovariantCLM_L2` at the TRIVIAL background on `L'`, as an identity of `L²` elements. -/
theorem coarsePlaqFnL2Equiv_coarseCurlCLM_L2 {ell : ℕ} (h : ScaleQuotient L ell L')
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseFnL2 L ell) :
    coarsePlaqFnL2Equiv h (AdalyFormal.MechEdges.G16.coarseCurlCLM_L2 hdvd B)
      = curlCovariantCLM_L2 (trivialU L') (coarseFnL2Equiv h B) := by
  apply (WithLp.linearEquiv 2 ℝ (PeriodicLatticePlaquette L' → SuTwo)).injective
  funext p
  show WithLp.ofLp (coarsePlaqFnL2Equiv h
      (AdalyFormal.MechEdges.G16.coarseCurlCLM_L2 hdvd B)) p
    = WithLp.ofLp (curlCovariantCLM_L2 (trivialU L') (coarseFnL2Equiv h B)) p
  rw [coarsePlaqFnL2Equiv_apply, ofLp_curlCovariantCLM_L2,
    AdalyFormal.MechEdges.G16.coarseCurlCLM_L2_apply,
    coarseCurlSuTwo_transport h hdvd (WithLp.ofLp B) ((coarsePlaqEquiv h).symm p),
    (coarsePlaqEquiv h).apply_symm_apply]
  rfl

/-- **THE COVARIANTISED COARSE CURL, CROSSED.**  Same identity with the background: `∂₁'(Ū)` IS
`curlCovariantCLM_L2` at the TRANSPORTED background. -/
theorem coarsePlaqFnL2Equiv_coarseCurlCovCLM_L2 {ell : ℕ} (h : ScaleQuotient L ell L')
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (V : CoarseLinkConfiguration L ell)
    (B : CoarseFnL2 L ell) :
    coarsePlaqFnL2Equiv h (coarseCurlCovCLM_L2 hdvd V B)
      = curlCovariantCLM_L2 (fun b => V ((coarseBondEquiv h).symm b)) (coarseFnL2Equiv h B) := by
  apply (WithLp.linearEquiv 2 ℝ (PeriodicLatticePlaquette L' → SuTwo)).injective
  funext p
  show WithLp.ofLp (coarsePlaqFnL2Equiv h (coarseCurlCovCLM_L2 hdvd V B)) p
    = WithLp.ofLp (curlCovariantCLM_L2 (fun b => V ((coarseBondEquiv h).symm b))
        (coarseFnL2Equiv h B)) p
  rw [coarsePlaqFnL2Equiv_apply, ofLp_curlCovariantCLM_L2, coarseCurlCovCLM_L2_apply,
    coarseCurlSuTwoCov_transport h hdvd V (WithLp.ofLp B) ((coarsePlaqEquiv h).symm p),
    (coarsePlaqEquiv h).apply_symm_apply]
  rfl

/-- The norm consequence of the first crossing identity — this is the equality that lets
`MechG16.hraw_op`'s LEFT-HAND SIDE be read as a covariant curl on the SMALLER torus. -/
theorem norm_coarseCurlCLM_L2_eq {ell : ℕ} (h : ScaleQuotient L ell L')
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : CoarseFnL2 L ell) :
    ‖AdalyFormal.MechEdges.G16.coarseCurlCLM_L2 hdvd B‖
      = ‖curlCovariantCLM_L2 (trivialU L') (coarseFnL2Equiv h B)‖ := by
  rw [← coarsePlaqFnL2Equiv_coarseCurlCLM_L2 h hdvd B, norm_coarsePlaqFnL2Equiv]

/-! ## §7 — THE PAYOFF: `hraw` AT THE COMPOSED CARRIERS

`compute/terminal_assembly/SCOPE.md` §3b's table asks for the shape

    ∀ A : Hs,  ‖curlCovariantCLM_L2 U (D.Q A)‖ ≤ σ₀·‖d A‖ + κ·‖D.Q A‖

at `Hs → BondFnL2 L'` at general `U`, where the tree had `hraw_op` only between
`BondFnL2 L → CoarseFnL2 L ell` with the FLAT coarse curl.  §7 supplies it with
`Hs := BondFnL2 L` for a FINER torus `L` (`ScaleQuotient L ell L'`) and
`D.Q := composedQ`.  Note the error term of the consumer's shape is measured on the COARSE side
(`κ‖D.Q A‖`), whereas `hraw_op`'s is on the FINE side (`c‖A‖`); §7c is where that difference is paid
and §7d is where it is NOT paid. -/

/-- **THE COMPOSED CONSTRAINT OPERATOR.**  Block-average at scale `ell` on the fine torus `L`,
then the extent identification: `BondFnL2 L →L[ℝ] BondFnL2 L'`.  The second factor is an ISOMETRY
(§3a), so `‖D.Q A‖` means the same number on either side of it. -/
noncomputable def composedQ {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    BondFnL2 L →L[ℝ] BondFnL2 L' :=
  ((coarseFnL2Equiv h).toContinuousLinearEquiv.toContinuousLinearMap).comp (qCLM Ufine ell)

theorem composedQ_apply {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : BondFnL2 L) : composedQ h Ufine A = coarseFnL2Equiv h (qCLM Ufine ell A) := rfl

/-! ### §7a — the single-scale drift at the COARSE level, at the operator norm -/

/-- `‖D_U X − D_1 X‖` on `L'`, as the drift energy `RegularUPerturbation` controls. -/
theorem norm_curl_sub_flat
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (X : BondFnL2 L') :
    ‖curlCovariantCLM_L2 U X - curlCovariantCLM_L2 (trivialU L') X‖
      = Real.sqrt (plaqEnergy (curlDrift U (WithLp.ofLp X))) := by
  rw [pilp_norm_eq_sqrt_sum]
  unfold plaqEnergy
  refine congrArg Real.sqrt (Finset.sum_congr rfl (fun p _ => ?_))
  refine congrArg (fun t : ℝ => t ^ 2) (congrArg norm ?_)
  show WithLp.ofLp (curlCovariantCLM_L2 U X) p - WithLp.ofLp (curlCovariantCLM_L2 (trivialU L') X) p
      = _
  rw [ofLp_curlCovariantCLM_L2, ofLp_curlCovariantCLM_L2]
  rfl

/-- **THE COVARIANT CURL IS THE FLAT ONE UP TO A DRIFT PRICED BY `α₁`**, at the operator level on
`L'`.  Constant `4√2`, `RegularUPerturbation`'s (REUSED). -/
theorem norm_curlCov_le_flat_add_drift
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (X : BondFnL2 L') :
    ‖curlCovariantCLM_L2 U X‖
      ≤ ‖curlCovariantCLM_L2 (trivialU L') X‖ + 4 * Real.sqrt 2 * frobSupBond U * ‖X‖ := by
  have htri : ‖curlCovariantCLM_L2 U X‖
      ≤ ‖curlCovariantCLM_L2 (trivialU L') X‖
        + ‖curlCovariantCLM_L2 U X - curlCovariantCLM_L2 (trivialU L') X‖ := by
    have := norm_add_le (curlCovariantCLM_L2 (trivialU L') X)
      (curlCovariantCLM_L2 U X - curlCovariantCLM_L2 (trivialU L') X)
    simpa using this
  have hdr : ‖curlCovariantCLM_L2 U X - curlCovariantCLM_L2 (trivialU L') X‖
      ≤ 4 * Real.sqrt 2 * frobSupBond U * ‖X‖ := by
    rw [norm_curl_sub_flat U X]
    have hb := norm_curlDrift_L2_le_sup U (WithLp.ofLp X)
    rwa [← norm_bondFnL2 (WithLp.ofLp X)] at hb
  linarith

/-! ### §7b — `hraw` AT THE COMPOSED CARRIERS, GENERAL FINE BACKGROUND (three terms) -/

/-- **THE COMPOSED CHAIN BOUND, GENERAL BACKGROUNDS ON BOTH LEVELS.**  Every term is a theorem of
the tree read through §3–§6:

    ‖D_U (Q A)‖ ≤ ℓ^{-1/2}·‖D_{U_fine} A‖ + (36√2·ℓ^{-1/2}·α₁(U_fine))·‖A‖ + 4√2·α₁(U)·‖Q A‖ .

The THIRD term has the consumer's shape `κ‖QA‖`; the SECOND does not — it is measured on the fine
carrier.  §7c removes it exactly when the fine background is flat, §7d prices it under a named
sufficient condition. -/
theorem hraw_composed_general {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U (composedQ h Ufine A)‖
      ≤ rawSigmaZero ell * ‖curlCovariantCLM_L2 Ufine A‖
        + rawErrorCoeff ell Ufine * ‖A‖
        + 4 * Real.sqrt 2 * frobSupBond U * ‖composedQ h Ufine A‖ := by
  have hdvd := dvd_of_scale h
  have h1 := norm_curlCov_le_flat_add_drift U (composedQ h Ufine A)
  have h2 : ‖curlCovariantCLM_L2 (trivialU L') (composedQ h Ufine A)‖
      = ‖coarseCurlCLM_L2 hdvd (qCLM Ufine ell A)‖ := by
    rw [composedQ_apply, ← norm_coarseCurlCLM_L2_eq h hdvd (qCLM Ufine ell A)]
  have h3 := hraw_op hdvd Ufine A
  rw [h2] at h1
  linarith

/-! ### §7c — THE CONSUMER'S EXACT SHAPE, AT A FLAT FINE BACKGROUND -/

/-- `rawErrorCoeff` vanishes at the trivial fine background — the whole content of §7c. -/
theorem rawErrorCoeff_trivialU (ell : ℕ) : rawErrorCoeff ell (trivialU L) = 0 := by
  unfold rawErrorCoeff
  rw [frobSupBond_trivialU L, mul_zero]

/-- **`hraw` IN EXACTLY `terminal_wired_posDef`'s BINDER SHAPE.**

    ∀ A : BondFnL2 L,  ‖D_U (Q A)‖ ≤ ℓ^{-1/2}·‖D_1 A‖ + (4√2·α₁(U))·‖Q A‖

with `Q = composedQ h 1` the honest block-average-then-identify map from the FINER torus `L` onto
`BondFnL2 L'`, and `U` an ARBITRARY background on `L'` — no smallness, no flatness on `U`.
`σ₀ = ℓ^{-1/2}`; `κ = 4√2·α₁(U)`.

**What is flat here and what is not, stated at the types:** the FINE background (the one `Q` and
`d` are built at) is `trivialU L`; the COARSE background `U` (the one `Δ_k` is evaluated at in
`terminal_wired_posDef`) is arbitrary.  §7d is the general-fine-background statement. -/
theorem hraw_composed_flatFine {ell : ℕ} (h : ScaleQuotient L ell L')
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U (composedQ h (trivialU L) A)‖
      ≤ rawSigmaZero ell * ‖curlCovariantCLM_L2 (trivialU L) A‖
        + 4 * Real.sqrt 2 * frobSupBond U * ‖composedQ h (trivialU L) A‖ := by
  have hg := hraw_composed_general h (trivialU L) U A
  rw [rawErrorCoeff_trivialU ell] at hg
  linarith

/-! ### §7d — THE GENERAL FINE BACKGROUND: THE NAMED SUFFICIENT CONDITION, AND ITS PRICE -/

/-- **THE FINE-SIDE TERM IS PAYABLE EXACTLY BY A LOWER BOUND ON `Q`.**  If `‖A‖ ≤ ρ‖QA‖` for every
`A` in the fine carrier, the three-term bound of §7b collapses to the consumer's two-term shape with

    κ = 4√2·α₁(U) + ρ·36√2·ℓ^{-1/2}·α₁(U_fine) .

This is a sufficiency statement, not an existence one: `composedQ` is a block AVERAGE and no such
`ρ` is claimed here for it (its kernel is exactly what would refute one).

**No sign hypothesis on `ρ` appears, deliberately**: at `ρ < 0` the hypothesis `hlow` already fails
on any nonzero `A` (it would assert `0 ≤ ‖A‖ ≤` a negative number), so adding `0 ≤ ρ` would be an
unused binder.  The proof uses only `rawErrorCoeff_nonneg`. -/
theorem hraw_composed_of_lower_bound {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (ρ : ℝ) (hlow : ∀ A : BondFnL2 L, ‖A‖ ≤ ρ * ‖composedQ h Ufine A‖)
    (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U (composedQ h Ufine A)‖
      ≤ rawSigmaZero ell * ‖curlCovariantCLM_L2 Ufine A‖
        + (4 * Real.sqrt 2 * frobSupBond U + ρ * rawErrorCoeff ell Ufine)
            * ‖composedQ h Ufine A‖ := by
  have hg := hraw_composed_general h Ufine U A
  have hc : rawErrorCoeff ell Ufine * ‖A‖
      ≤ rawErrorCoeff ell Ufine * (ρ * ‖composedQ h Ufine A‖) :=
    mul_le_mul_of_nonneg_left (hlow A) (rawErrorCoeff_nonneg ell Ufine)
  nlinarith [hg, hc]

/-! ### §7e — `composedQ` IS SURJECTIVE AT THE FLAT FINE BACKGROUND

Needed so that a covariance datum can be BUILT on it (`CovDataCtor.build` takes `Q` surjective), i.e.
so that §7c's `hraw` is a statement about an inhabited datum and not about an empty hypothesis. -/

theorem composedQ_surjective {ell : ℕ} (h : ScaleQuotient L ell L') :
    Function.Surjective (composedQ h (trivialU L)) := by
  intro y
  obtain ⟨x, hx⟩ := AdalyFormal.Balaban.BridgeInverse.qCLM_surjective_trivialU
    (ell_pos_of_scale h) (dvd_of_scale h) ((coarseFnL2Equiv h).symm y)
  refine ⟨x, ?_⟩
  rw [composedQ_apply, hx]
  exact (coarseFnL2Equiv h).apply_symm_apply y

/-! ### §7f — THE `StokesRestricted` SHAPE AT FULLY GENERAL BACKGROUNDS

`StokesCommu.Restricted`'s own consumer takes the error on the FINE carrier (`c‖A‖`), which is a
STRICTLY WEAKER demand than `terminal_wired_posDef`'s `κ‖D.Q A‖` (since `‖QA‖ ≤ ‖Q‖‖A‖`).  That
weaker shape is available with NO flatness and NO smallness anywhere. -/

theorem hraw_composed_fineNorm {ell : ℕ} (h : ScaleQuotient L ell L')
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L')
    (A : BondFnL2 L) :
    ‖curlCovariantCLM_L2 U (composedQ h Ufine A)‖
      ≤ rawSigmaZero ell * ‖curlCovariantCLM_L2 Ufine A‖
        + (rawErrorCoeff ell Ufine
            + 4 * Real.sqrt 2 * frobSupBond U * ‖composedQ h Ufine‖) * ‖A‖ := by
  have hg := hraw_composed_general h Ufine U A
  have hop : ‖composedQ h Ufine A‖ ≤ ‖composedQ h Ufine‖ * ‖A‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hc : (0 : ℝ) ≤ 4 * Real.sqrt 2 * frobSupBond U :=
    mul_nonneg (by positivity) (frobSupBond_nonneg U)
  nlinarith [hg, hop, hc]

/-! ## §8 — GUARDS

Three of them, all decidable on concrete data:

* **§8a** the divisibility direction, against `compute/kimi_stake_u6/src/U6_counterexample.lean`'s own
  truncation data (`L = fun _ => 2`, `ell = 2`, `2 ∤ 3`);
* **§8b** the reason a CARDINALITY check would NOT have caught it — the index sets are equinumerous
  there, so an index-set bijection EXISTS; what the hypothesis buys is shift-compatibility;
* **§8c** object 2 is genuinely background-dependent (S82: not the flat operator in disguise). -/

/-- The `U6` counterexample's extent: every side length is `2 + 1 = 3`. -/
def cexL : PeriodicLatticeExtent := fun _ => 2

/-- **§8a — NO SCALE QUOTIENT EXISTS AT `ell = 2` ON THE `U6` TORUS.**  `2·(k+1) = 3` has no
solution, so `ScaleQuotient cexL 2 L'` is uninhabited for EVERY `L'`: the extent identification
cannot even be stated there.  This is the negation anchor for the divisibility direction — a
mutation that drops the scale hypothesis from `coarseSiteEquiv` has to contradict this. -/
theorem no_scaleQuotient_at_u6 : ¬ ∃ L' : PeriodicLatticeExtent, ScaleQuotient cexL 2 L' := by
  rintro ⟨L', h⟩
  have hcon : 2 * (L' 0 + 1) = 3 := h 0
  omega

/-- **§8a′ — THE MECHANISM.**  At the same data the coarse lattice is not closed under its own
adjacency: the boundary coarse site `(2,2,2)` shifted by `ell = 2` in direction `0` lands on
coordinate `(2+2) % 3 = 1`, which is not a multiple of `2`.  So `coarseCurlSuTwo` is not even
well-typed there — the `hdvd` argument of `coarseShift_mem_coarseLattice` is doing real work. -/
theorem coarseShift_escapes_at_u6 :
    coarseShift (fun _ => 2 : PeriodicLatticeSite cexL) 2 0 ∉ CoarseLattice cexL 2 := by
  decide

/-- **§8b — CARDINALITY WOULD NOT HAVE CAUGHT IT.**  On the `U6` data the coarse bond set has
exactly as many elements as the bond set of the side-`2` torus, so a bijection of INDEX SETS exists
there even though no `ScaleQuotient` does (§8a).  Stated so that nobody reads `coarseBondEquiv` as a
counting fact: what the scale hypothesis buys is `coarseSiteEquiv_coarseShift`, not a count. -/
theorem card_coarseBond_u6 : Fintype.card (CoarseBond cexL 2) = 24 := by decide

theorem card_bond_side_two : Fintype.card (Bond (fun _ => 1 : PeriodicLatticeExtent)) = 24 := by
  decide

/-- The index-set bijection that EXISTS at the truncated data, exhibited. -/
noncomputable def u6_index_bijection : CoarseBond cexL 2 ≃ Bond (fun _ => 1 : PeriodicLatticeExtent) :=
  Fintype.equivOfCardEq (by rw [card_coarseBond_u6, card_bond_side_two])

/-! ### §8c — object 2 is not the flat operator in disguise -/

/-- A tiled extent: side length `4`, so `ell = 2` divides it. -/
def gL : PeriodicLatticeExtent := fun _ => 3

theorem gL_hdvd : ∀ μ : Fin 3, (2 : ℕ) ∣ (gL μ + 1) := by decide

/-- `ScaleQuotient` IS inhabited here, with `L' = ` side-`2` torus — a positive control for §8a. -/
theorem gL_scaleQuotient : ScaleQuotient gL 2 (fun _ => 1) := fun _ => rfl

def gY : PeriodicLatticeSite gL := fun _ => 0

theorem gY_mem : gY ∈ CoarseLattice gL 2 := by decide

def gP : CoarsePlaquette gL 2 := (⟨gY, gY_mem⟩, ⟨(0, 1), by decide⟩)

/-- The single coarse bond the test field is supported on: the `ν`-bond at the `μ`-shifted corner,
i.e. the one carrying the SECOND term of the four-term curl — the first of the two terms object 2
conjugates. -/
def gB0 : CoarseBond gL 2 :=
  (⟨coarseShift gY 2 0, coarseShift_mem_coarseLattice gL_hdvd gY_mem 0⟩, 1)

noncomputable def gB : CoarseBond gL 2 → SuTwo :=
  fun b => if b = gB0 then AdalyFormal.Balaban.CovariantOperators.suTwoWitness else 0

noncomputable def gV : CoarseLinkConfiguration gL 2 :=
  fun _ => AdalyFormal.Balaban.CovariantOperators.witnessMElem

theorem g_flat : coarseCurlSuTwo gL_hdvd gB gP
    = AdalyFormal.Balaban.CovariantOperators.suTwoWitness := by
  show gB (gP.1, (0 : Fin 3)) + gB (⟨coarseShift gP.1.1 2 0, _⟩, (1 : Fin 3))
      - gB (⟨coarseShift gP.1.1 2 1, _⟩, (0 : Fin 3)) - gB (gP.1, (1 : Fin 3)) = _
  unfold gB
  rw [if_neg (by decide : ¬((gP.1, (0 : Fin 3)) = gB0)),
    if_pos (by rfl : ((⟨coarseShift gP.1.1 2 0,
      coarseShift_mem_coarseLattice gL_hdvd gP.1.2 0⟩, (1 : Fin 3)) : CoarseBond gL 2) = gB0),
    if_neg (by decide : ¬((⟨coarseShift gP.1.1 2 1,
      coarseShift_mem_coarseLattice gL_hdvd gP.1.2 1⟩, (0 : Fin 3)) = gB0)),
    if_neg (by decide : ¬((gP.1, (1 : Fin 3)) = gB0))]
  abel

theorem g_cov : coarseCurlSuTwoCov gL_hdvd gV gB gP
    = -AdalyFormal.Balaban.CovariantOperators.suTwoWitness := by
  show gB (gP.1, (0 : Fin 3))
      + RMap (gV (gP.1, (0 : Fin 3))) (gB (⟨coarseShift gP.1.1 2 0, _⟩, (1 : Fin 3)))
      - RMap (gV (gP.1, (1 : Fin 3))) (gB (⟨coarseShift gP.1.1 2 1, _⟩, (0 : Fin 3)))
      - gB (gP.1, (1 : Fin 3)) = _
  unfold gB gV
  rw [if_neg (by decide : ¬((gP.1, (0 : Fin 3)) = gB0)),
    if_pos (by rfl : ((⟨coarseShift gP.1.1 2 0,
      coarseShift_mem_coarseLattice gL_hdvd gP.1.2 0⟩, (1 : Fin 3)) : CoarseBond gL 2) = gB0),
    if_neg (by decide : ¬((⟨coarseShift gP.1.1 2 1,
      coarseShift_mem_coarseLattice gL_hdvd gP.1.2 1⟩, (0 : Fin 3)) = gB0)),
    if_neg (by decide : ¬((gP.1, (1 : Fin 3)) = gB0)),
    AdalyFormal.Balaban.CovariantOperators.RMap_witnessMElem, map_zero]
  abel

/-- **§8c — OBJECT 2 GENUINELY CARRIES THE BACKGROUND.**  On concrete data the covariantised coarse
curl and the flat one take DIFFERENT values (`−w` against `w`, `w ≠ 0`), so
`coarseCurlSuTwoCov_trivial` is a real reduction and not an identity in disguise. -/
theorem coarseCurlSuTwoCov_ne_coarseCurlSuTwo :
    coarseCurlSuTwoCov gL_hdvd gV gB gP ≠ coarseCurlSuTwo gL_hdvd gB gP := by
  rw [g_cov, g_flat]
  intro hcon
  have h2 : (2 : ℝ) • AdalyFormal.Balaban.CovariantOperators.suTwoWitness = 0 := by
    rw [two_smul]
    have := congrArg (fun x => x + AdalyFormal.Balaban.CovariantOperators.suTwoWitness) hcon
    simpa using this.symm
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero h

/-! ## §9 — THE CARRIER DROP IS REAL: `composedQ` IS NOT INJECTIVE

`compute/terminal_assembly/SCOPE.md` §7 residual 2 asks for an inhabitant with `dim Hs > dim Ks`.
§9 proves the dimension count that makes that true for `composedQ`: the fine torus has `ell³` times
as many bonds, so at `ell ≥ 2` no injective linear map `BondFnL2 L → BondFnL2 L'` exists at all — in
particular `composedQ`, which §7e shows is SURJECTIVE, is not bijective. -/

theorem card_site_eq_prod (M : PeriodicLatticeExtent) :
    Fintype.card (PeriodicLatticeSite M) = ∏ μ : Fin 3, (M μ + 1) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl (fun μ _ => Fintype.card_fin _)

theorem card_bond_eq (M : PeriodicLatticeExtent) :
    Fintype.card (Bond M) = (∏ μ : Fin 3, (M μ + 1)) * 3 := by
  show Fintype.card (PeriodicLatticeSite M × Fin 3) = _
  rw [Fintype.card_prod, card_site_eq_prod, Fintype.card_fin]

/-- **THE BOND COUNT SCALES BY `ell³`.** -/
theorem card_bond_scale {ell : ℕ} (h : ScaleQuotient L ell L') :
    Fintype.card (Bond L) = ell ^ 3 * Fintype.card (Bond L') := by
  rw [card_bond_eq, card_bond_eq]
  have hprod : (∏ μ : Fin 3, (L μ + 1)) = ell ^ 3 * ∏ μ : Fin 3, (L' μ + 1) := by
    rw [show (∏ μ : Fin 3, (L μ + 1)) = ∏ μ : Fin 3, (ell * (L' μ + 1)) from
      Finset.prod_congr rfl (fun μ _ => (h μ).symm), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  ring

theorem finrank_bondFnL2 (M : PeriodicLatticeExtent) :
    Module.finrank ℝ (BondFnL2 M) = Fintype.card (Bond M) * Module.finrank ℝ SuTwo := by
  rw [(WithLp.linearEquiv 2 ℝ (Bond M → SuTwo)).finrank_eq, Module.finrank_pi_fintype ℝ,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem finrank_suTwo_pos : 0 < Module.finrank ℝ SuTwo := Module.finrank_pos

/-- **NO INJECTIVE LINEAR MAP EXISTS FROM THE FINE CARRIER TO THE COARSE ONE AT `ell ≥ 2`.**
A dimension count, not a property of `composedQ`. -/
theorem no_injective_fine_to_coarse {ell : ℕ} (h : ScaleQuotient L ell L') (hell2 : 2 ≤ ell)
    (f : BondFnL2 L →ₗ[ℝ] BondFnL2 L') : ¬ Function.Injective f := by
  intro hinj
  have hle : Module.finrank ℝ (BondFnL2 L) ≤ Module.finrank ℝ (BondFnL2 L') :=
    f.finrank_le_finrank_of_injective hinj
  rw [finrank_bondFnL2, finrank_bondFnL2, card_bond_scale h] at hle
  have hd := finrank_suTwo_pos
  have hcard : 0 < Fintype.card (Bond L') := Fintype.card_pos
  have h8 : 8 ≤ ell ^ 3 := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ ell ^ 3 := Nat.pow_le_pow_left hell2 3
  rw [mul_assoc] at hle
  set C := Fintype.card (Bond L') * Module.finrank ℝ SuTwo with hC
  have hCpos : 0 < C := Nat.mul_pos hcard hd
  have h8C : 8 * C ≤ ell ^ 3 * C := Nat.mul_le_mul h8 (le_refl C)
  linarith

/-- **THE INHABITANT IS NOT COLLAPSED.**  `composedQ` is surjective (§7e) and NOT injective, so —
unlike `TerminalAssembly.assemblyDatum`'s `Q = I` — the minimisation defining `Φ_a` is over a
positive-dimensional affine fibre. -/
theorem composedQ_not_injective {ell : ℕ} (h : ScaleQuotient L ell L') (hell2 : 2 ≤ ell)
    (Ufine : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    ¬ Function.Injective (composedQ h Ufine) :=
  no_injective_fine_to_coarse h hell2 (composedQ h Ufine).toLinearMap

#print axioms ScaleQuotient
#print axioms ell_pos_of_scale
#print axioms dvd_of_scale
#print axioms coarseSiteFwd
#print axioms coarseSiteBwd
#print axioms coarseSiteEquiv
#print axioms coarseSiteEquiv_val
#print axioms coarseSiteEquiv_symm_val
#print axioms shift_val_eq
#print axioms coarseSiteEquiv_coarseShift
#print axioms coarseBondEquiv
#print axioms coarsePlaqEquiv
#print axioms coarseBondEquiv_apply
#print axioms coarsePlaqEquiv_apply
#print axioms coarseFnL2Equiv
#print axioms coarsePlaqFnL2Equiv
#print axioms norm_coarseFnL2Equiv
#print axioms inner_coarseFnL2Equiv
#print axioms norm_coarsePlaqFnL2Equiv
#print axioms coarseFnL2Equiv_apply
#print axioms coarsePlaqFnL2Equiv_apply
#print axioms coarseBondEquiv_symm_apply
#print axioms coarseCurlSuTwo_transport
#print axioms CoarseLinkConfiguration
#print axioms coarseCurlSuTwoCov
#print axioms trivialCoarseU
#print axioms coarseCurlSuTwoCov_trivial
#print axioms coarseCurlSuTwoCov_transport
#print axioms coarseCurlSuTwoCov_sub_flat
#print axioms coarse_drift_energy_le
#print axioms coarseCurlCovLM
#print axioms coarseCurlCovCLM_L2
#print axioms coarseCurlCovCLM_L2_apply
#print axioms ofLp_curlCovariantCLM_L2
#print axioms coarsePlaqFnL2Equiv_coarseCurlCLM_L2
#print axioms coarsePlaqFnL2Equiv_coarseCurlCovCLM_L2
#print axioms norm_coarseCurlCLM_L2_eq
#print axioms composedQ
#print axioms composedQ_apply
#print axioms norm_curl_sub_flat
#print axioms norm_curlCov_le_flat_add_drift
#print axioms hraw_composed_general
#print axioms rawErrorCoeff_trivialU
#print axioms hraw_composed_flatFine
#print axioms hraw_composed_of_lower_bound
#print axioms composedQ_surjective
#print axioms hraw_composed_fineNorm
#print axioms cexL
#print axioms no_scaleQuotient_at_u6
#print axioms coarseShift_escapes_at_u6
#print axioms card_coarseBond_u6
#print axioms card_bond_side_two
#print axioms u6_index_bijection
#print axioms gL
#print axioms gL_hdvd
#print axioms gL_scaleQuotient
#print axioms gY
#print axioms gY_mem
#print axioms gP
#print axioms gB0
#print axioms gB
#print axioms gV
#print axioms g_flat
#print axioms g_cov
#print axioms coarseCurlSuTwoCov_ne_coarseCurlSuTwo
#print axioms card_site_eq_prod
#print axioms card_bond_eq
#print axioms card_bond_scale
#print axioms finrank_bondFnL2
#print axioms finrank_suTwo_pos
#print axioms no_injective_fine_to_coarse
#print axioms composedQ_not_injective

end AdalyFormal.HrawCarriers
