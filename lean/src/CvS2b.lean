import CvS2a

/-!
# CvS2b -- on the CvN6 TIP instance, `Δ^{(2)}` and the `J`-term of (3.156) vanish for EVERY link value
(lane cover_strong_20261016)

Instance: `tipP ell M R v a Λ` = the genuine parameters at height `k = 1` on GenCl's isolated-block tower `gcS ell M R`, with
`U = 1[b_t ↦ v]`, `b_t = (x_t, 1)` the tip bond (CvN6), any `v ∈ SU(2)`, any `a`, any `Λ`.  Hypotheses `3 ≤ ell`, `0 < M`,
`9 ell + 1 ≤ R` (those of CvN6 `tip_far9`).

* `JfieldLoc_update_support`: for `U = 1[b_t ↦ v]` and any plaquette set `P`, `J(x, μ) ≠ 0` only if some `q ∈ P` has BOTH `b_t` and
  `(x, μ)` among its boundary bonds.
* `tip_Jf_support`: on the tip instance every bond carrying `J ≠ 0` is a LEVEL-0 bond of `𝔅` (`bondsLam _ 0`): it lies on a
  plaquette of `plaqIn Ω₀` through `b_t`, so its endpoints are in `Ω₀` and within distance 4 of `x_t`, hence outside `Ω₁`.
* `tip_J_lvl0`: `⟪x, J⟫ = 0` for every `x ∈ E₀` whose `Q x` has zero level-0 coordinates (`Q₀ = id`).
* **`tip_G1inv_eq_Ginv`**: `G₁⁻¹ = G⁻¹` (3.128 = 3.122): the `Δ^{(2)}` term is zero for every `v`.
* **`tip_Jterm_zero`**: `⟪H₁ D̃⁽²⁾ B, J⟫ = 0` for every `v` and every `B`.
* **`tip_genForm_eq`**: `genForm B = η ⟪τ*B, (Q G Q*)⁻¹ τ*B⟫ − a ⟪B, B⟫` (`G = (G⁻¹)⁻¹` of (3.122), `Ring.inverse` as encoded).
* **`tip_WellDefG_iff`** (`a > 0`): `WellDefG ↔ (hb) ∧ IsUnit G⁻¹ ∧ IsUnit (Q G Q*)`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverStrong

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (FnuMuLoc JfieldLoc JSU2Loc)
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 conjByAmbient conjByAmbient_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.StatementLaneR6 (edge_mem imHolonomy_congr)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.NoCover
open AdalyFormal.GeneralClass
open AdalyFormal.CoverNec (tip_far9 tip_outside DelpA_unit imHol_one)

abbrev SU2c := Matrix.specialUnitaryGroup (Fin 2) ℂ

section Generic
variable {L : PeriodicLatticeExtent}

theorem imHol_update_zero (bt : Bond L) (v : SU2c) (q : PeriodicLatticePlaquette L)
    (hq : bt ∉ periodicPlaquetteBoundaryEdges q) :
    imHolonomy (Function.update (fun _ : Bond L => (1 : SU2c)) bt v) q = 0 := by
  rw [imHolonomy_congr (U' := fun _ : Bond L => (1 : SU2c)) (fun e he => ?_)]
  · exact imHol_one q
  · rw [Function.update_of_ne]
    rintro rfl
    exact hq he

theorem FnuMuLoc_update_zero (P : Set (PeriodicLatticePlaquette L)) (bt : Bond L) (v : SU2c) (ν μ : Fin 3)
    (y : PeriodicLatticeSite L) (e : Bond L)
    (hno : ∀ q ∈ P, bt ∈ periodicPlaquetteBoundaryEdges q → e ∉ periodicPlaquetteBoundaryEdges q)
    (he : ∀ hlt : ν < μ, e ∈ periodicPlaquetteBoundaryEdges
      ((y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) : PeriodicLatticePlaquette L))
    (he' : ∀ hgt : μ < ν, e ∈ periodicPlaquetteBoundaryEdges
      ((y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) : PeriodicLatticePlaquette L)) :
    FnuMuLoc P (Function.update (fun _ : Bond L => (1 : SU2c)) bt v) ν μ y = 0 := by
  unfold FnuMuLoc
  split_ifs with h1 h2 h3 h4
  · rw [imHol_update_zero bt v _ (fun hb => hno _ h2 hb (he h1))]
    unfold piProj; simp
  · rfl
  · rw [imHol_update_zero bt v _ (fun hb => hno _ h4 hb (he' h3))]
    unfold piProj; simp
  · rfl
  · rfl

/-- `J(x, μ) ≠ 0` at `U = 1[b_t ↦ v]` only if a plaquette of `P` carries both `b_t` and `(x, μ)`. -/
theorem JfieldLoc_update_support (P : Set (PeriodicLatticePlaquette L)) (bt : Bond L) (v : SU2c)
    (x : PeriodicLatticeSite L) (μ : Fin 3)
    (h : JfieldLoc P (Function.update (fun _ : Bond L => (1 : SU2c)) bt v) x μ ≠ 0) :
    ∃ q ∈ P, bt ∈ periodicPlaquetteBoundaryEdges q ∧ ((x, μ) : Bond L) ∈ periodicPlaquetteBoundaryEdges q := by
  by_contra hno
  push_neg at hno
  apply h
  unfold AdalyFormal.IngredientFamily.JfieldLoc
  refine Finset.sum_eq_zero (fun ν _ => ?_)
  split_ifs with hνμ
  · rfl
  · simp only [DstarDir]
    rw [FnuMuLoc_update_zero P bt v ν μ x (x, μ) hno
          (fun _ => (edge_mem _ _).mpr (Or.inr (Or.inr (Or.inr rfl))))
          (fun _ => (edge_mem _ _).mpr (Or.inl rfl)),
        FnuMuLoc_update_zero P bt v ν μ (periodicLatticeShiftBack x ν) (x, μ) hno
          (fun _ => (edge_mem _ _).mpr (Or.inr (Or.inl (by simp [periodicLatticeShift_shiftBack]))))
          (fun _ => (edge_mem _ _).mpr (Or.inr (Or.inr (Or.inl (by simp [periodicLatticeShift_shiftBack])))))]
    simp [conjByAmbient_apply]

theorem JSU2Loc_zero_of (η : ℝ) (P : Set (PeriodicLatticePlaquette L)) (U : PeriodicLinkConfiguration SU2c L)
    (b : Bond L) (h : JfieldLoc P U b.1 b.2 = 0) : JSU2Loc η P U b = 0 := by
  apply Subtype.ext
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P U b.1 b.2 = ((0 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
  rw [h, smul_zero]
  simp

/-- every endpoint of a boundary bond of `q` is within `ℓ¹`-distance 2 of the corner `q.1`. -/
theorem plaq_corner_dist (q : PeriodicLatticePlaquette L) (e : Bond L) (he : e ∈ periodicPlaquetteBoundaryEdges q) :
    pdist q.1 e.1 ≤ 2 ∧ pdist q.1 (periodicLatticeShift e.1 e.2) ≤ 2 := by
  have s1 := AdalyFormal.StatementLaneR8.pdist_shift_le q.1 q.2.1.1
  have s2 := AdalyFormal.StatementLaneR8.pdist_shift_le q.1 q.2.1.2
  have s0 := AdalyFormal.StatementLaneR8.pdist_self q.1
  rcases (edge_mem q e).mp he with rfl | rfl | rfl | rfl
  · exact ⟨by simp only; omega, by simp only; omega⟩
  · refine ⟨by simp only; omega, ?_⟩
    have t := AdalyFormal.StatementLaneR8.pdist_triangle q.1 (periodicLatticeShift q.1 q.2.1.1)
      (periodicLatticeShift (periodicLatticeShift q.1 q.2.1.1) q.2.1.2)
    have s3 := AdalyFormal.StatementLaneR8.pdist_shift_le (periodicLatticeShift q.1 q.2.1.1) q.2.1.2
    simp only; omega
  · refine ⟨by simp only; omega, ?_⟩
    have t := AdalyFormal.StatementLaneR8.pdist_triangle q.1 (periodicLatticeShift q.1 q.2.1.2)
      (periodicLatticeShift (periodicLatticeShift q.1 q.2.1.2) q.2.1.1)
    have s3 := AdalyFormal.StatementLaneR8.pdist_shift_le (periodicLatticeShift q.1 q.2.1.2) q.2.1.1
    simp only; omega
  · exact ⟨by simp only; omega, by simp only; omega⟩

end Generic

/-! ## the tip instance -/

/-- the genuine parameters on the tip instance, link value `v` at the tip bond. -/
noncomputable abbrev tipP (ell M R : ℕ) (hell0 : 0 < ell) (hM : 0 < M) (v : SU2c) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite (ncLu M R))) : IngrBParams :=
  gparams ell 1 (ncLu M R) hell0 (gcS ell M R)
    (Function.update (fun _ => 1) ((xtG ell M R hell0 hM, 1) : Bond _) v) a Lam

section Tip
variable {ell M R : ℕ} (hell : 3 ≤ ell) (hell0 : 0 < ell) (hM : 0 < M) (hR : 9 * ell + 1 ≤ R)
  (v : SU2c) (a : ℝ) (Lam : Set (PeriodicLatticeSite (ncLu M R)))
include hell hR

theorem tip_Jf_support (b : Bond (scaleUp ell 1 (ncLu M R)))
    (hb : (WithLp.ofLp (tipP ell M R hell0 hM v a Lam).Jf) b ≠ 0) :
    b ∈ bondsLam (geomOf ell 1 (gcS ell M R)) 0 := by
  set bt : Bond (scaleUp ell 1 (ncLu M R)) := (xtG ell M R hell0 hM, 1) with hbt
  have hJ : JfieldLoc (plaqIn ((gcS ell M R).Om 0)) (Function.update (fun _ => 1) bt v) b.1 b.2 ≠ 0 := by
    intro h0
    apply hb
    show -(JSU2Loc 1 (plaqIn ((gcS ell M R).Om 0)) (Function.update (fun _ => 1) bt v) b) = 0
    rw [JSU2Loc_zero_of 1 _ _ b h0, neg_zero]
  obtain ⟨q, hq, hbtq, hbq⟩ := JfieldLoc_update_support _ bt v b.1 b.2 hJ
  have hfar := tip_far9 (R := R) hell hell0 hM hR
  have hqt : pdist q.1 (xtG ell M R hell0 hM) ≤ 2 := (plaq_corner_dist q bt hbtq).1
  have hqb := plaq_corner_dist q b hbq
  have hin : b.1 ∈ (gcS ell M R).Om 0 ∧ periodicLatticeShift b.1 b.2 ∈ (gcS ell M R).Om 0 := hq b hbq
  have hnot : ∀ z, pdist q.1 z ≤ 2 → z ∉ (gcS ell M R).Om 1 := by
    intro z hz hz1
    have h1 := hfar z hz1
    have h2 := AdalyFormal.StatementLaneR8.pdist_triangle z q.1 (xtG ell M R hell0 hM)
    rw [AdalyFormal.StatementLaneR8.pdist_comm z q.1] at h2
    omega
  have hadm := gc_admissible (R := R) hell0 hM
  have hcs : coarseShift b.1 (ell ^ 0) b.2 = periodicLatticeShift b.1 b.2 := by
    rw [pow_zero]; rfl
  refine ⟨Or.inl ⟨fun μ => by simp, hin.1, hnot _ hqb.1⟩, ?_⟩
  show ¬ (OmGe (geomOf ell 1 (gcS ell M R)) (0 + 1) b.1 ∨
    OmGe (geomOf ell 1 (gcS ell M R)) (0 + 1) (coarseShift b.1 (ell ^ 0) b.2))
  rw [hcs]
  rintro (h | h)
  · exact hnot _ hqb.1 ((omGe_iff_om ell M R 1 hell0 _ hadm 1 _).mp h)
  · exact hnot _ hqb.2 ((omGe_iff_om ell M R 1 hell0 _ hadm 1 _).mp h)

theorem tip_J_lvl0 :
    ∀ x : ↥(bondSupp (tipP ell M R hell0 hM v a Lam).G),
      Lvl0Zero (tipP ell M R hell0 hM v a Lam).G ((tipP ell M R hell0 hM v a Lam).data.Q x) →
        ⟪x, (tipP ell M R hell0 hM v a Lam).data.J⟫ = 0 := by
  intro x hx
  show ⟪x, pE (tipP ell M R hell0 hM v a Lam).G (tipP ell M R hell0 hM v a Lam).Jf⟫ = 0
  rw [pE_inner_right, PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  by_cases hb : (WithLp.ofLp (tipP ell M R hell0 hM v a Lam).Jf) b = 0
  · rw [hb, inner_zero_right]
  · have hmem := tip_Jf_support hell hell0 hM hR v a Lam b hb
    have h0 := hx ⟨0, ⟨b, hmem⟩⟩ rfl
    rw [data_Q_lvl0 _ x _ rfl] at h0
    rw [h0, inner_zero_left]

/-- **`G₁⁻¹ = G⁻¹` on the tip instance, for every `v`**: the `Δ^{(2)}` term of (3.128) is zero. -/
theorem tip_G1inv_eq_Ginv : (tipP ell M R hell0 hM v a Lam).G1inv = (tipP ell M R hell0 hM v a Lam).data.Ginv :=
  G1inv_eq_Ginv_of (tipP ell M R hell0 hM v a Lam).data (tipP ell M R hell0 hM v a Lam).data_laws
    (Lvl0Zero (tipP ell M R hell0 hM v a Lam).G) (tip_J_lvl0 hell hell0 hM hR v a Lam)
    (data_C2_lvl0 _) (tipP ell M R hell0 hM v a Lam).G1inv_spec

/-- **the `J`-term of (3.156) is zero on the tip instance, for every `v` and every `B`.** -/
theorem tip_Jterm_zero (B : BondFnL2 (ncLu M R)) :
    ⟪(tipP ell M R hell0 hM v a Lam).H1in ((tipP ell M R hell0 hM v a Lam).D2in B),
      (tipP ell M R hell0 hM v a Lam).Jf⟫ = 0 := by
  show ⟪iE (tipP ell M R hell0 hM v a Lam).G ((tipP ell M R hell0 hM v a Lam).data.H1
      (tipP ell M R hell0 hM v a Lam).G1inv
      (ContinuousLinearMap.adjoint (tipP ell M R hell0 hM v a Lam).tau ((tipP ell M R hell0 hM v a Lam).D2in B))),
      (tipP ell M R hell0 hM v a Lam).Jf⟫ = 0
  rw [← pE_inner_right]
  exact H1_pair_zero (tipP ell M R hell0 hM v a Lam).data (Lvl0Zero (tipP ell M R hell0 hM v a Lam).G)
    (tip_J_lvl0 hell hell0 hM hR v a Lam) _ (tau_adj_lvl0 _ le_rfl _)

theorem tip_Nmat_eq : GenP.Nmat (tipP ell M R hell0 hM v a Lam) =
    ((tipP ell M R hell0 hM v a Lam).data.Q.comp (tipP ell M R hell0 hM v a Lam).data.G).comp
      (tipP ell M R hell0 hM v a Lam).data.Qs := by
  unfold GenP.Nmat BaseDataS.G1
  rw [tip_G1inv_eq_Ginv hell hell0 hM hR v a Lam]
  rfl

/-- **(3.156) on the tip instance**: `genForm B = η ⟪τ*B, (Q G Q*)⁻¹ τ*B⟫ − a ⟪B, B⟫`, for every `v`. -/
theorem tip_genForm_eq (B : BondFnL2 (ncLu M R)) :
    GenP.genForm (tipP ell M R hell0 hM v a Lam) B =
      (tipP ell M R hell0 hM v a Lam).eta *
        ⟪ContinuousLinearMap.adjoint (tipP ell M R hell0 hM v a Lam).tau B,
          Ring.inverse (((tipP ell M R hell0 hM v a Lam).data.Q.comp (tipP ell M R hell0 hM v a Lam).data.G).comp
            (tipP ell M R hell0 hM v a Lam).data.Qs)
            (ContinuousLinearMap.adjoint (tipP ell M R hell0 hM v a Lam).tau B)⟫ - a * ⟪B, B⟫ := by
  unfold GenP.genForm GenP.firstTerm
  rw [tip_Nmat_eq hell hell0 hM hR v a Lam, tip_Jterm_zero hell hell0 hM hR v a Lam]
  have : (tipP ell M R hell0 hM v a Lam).a = a := rfl
  rw [this]
  ring

/-- **`WellDefG` on the tip instance** (`a > 0`): hb, `G⁻¹` invertible, `Q G Q*` invertible. -/
theorem tip_WellDefG_iff (ha : 0 < a) :
    GenP.WellDefG (tipP ell M R hell0 hM v a Lam) ↔
      Function.Bijective (H0 (tipP ell M R hell0 hM v a Lam).Lam (tipP ell M R hell0 hM v a Lam).Q1) ∧
        IsUnit (tipP ell M R hell0 hM v a Lam).data.Ginv ∧
        IsUnit (((tipP ell M R hell0 hM v a Lam).data.Q.comp (tipP ell M R hell0 hM v a Lam).data.G).comp
          (tipP ell M R hell0 hM v a Lam).data.Qs) := by
  have hD : IsUnit (DelpA (tipP ell M R hell0 hM v a Lam).G (tipP ell M R hell0 hM v a Lam).U
      (tipP ell M R hell0 hM v a Lam).a + (1 - siteMask (tipP ell M R hell0 hM v a Lam).G.Om0)) :=
    DelpA_unit (ell := ell) (gcS ell M R) _ ha (tip_outside hell hell0 hM (by omega))
  unfold GenP.WellDefG GenP.WellDef GenP.GuardsUnit
  rw [tip_G1inv_eq_Ginv hell hell0 hM hR v a Lam, tip_Nmat_eq hell hell0 hM hR v a Lam]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, -, -, -⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, h3⟩, hD, h2, h3⟩

end Tip

#print axioms imHol_update_zero
#print axioms FnuMuLoc_update_zero
#print axioms JfieldLoc_update_support
#print axioms JSU2Loc_zero_of
#print axioms plaq_corner_dist
#print axioms tip_Jf_support
#print axioms tip_J_lvl0
#print axioms tip_G1inv_eq_Ginv
#print axioms tip_Jterm_zero
#print axioms tip_Nmat_eq
#print axioms tip_genForm_eq
#print axioms tip_WellDefG_iff

end AdalyFormal.CoverStrong
