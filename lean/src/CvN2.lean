import ZR8Site
import ZR8DataA
import CvN1

/-!
# CvN2 -- locality AWAY from `Ω₁` (lane cover_necessary_20261016)

Height `k = 1`, any tower `S`.  `FarAgree S r U U'`: the two configurations agree on every bond based within `ℓ¹`-distance `r` of
`Ω₁`.  Under `FarAgree S (9 ell) U U'` every `Q`-dependent object of (3.122) is THE SAME for `U` and `U'`:
`Q'_j` rows (`Qlev`), `Q'*aQ'` (`Qpa`), `N(Q')`, `Δ_U N(Q')` (`RImage`), `R`, `T = R D*` (`Tfull`), the bond-sector `Q`
(`QfullOf`) and the mass term `Q*aQ` (`MassFull`).  (The r8 lane's own locality theorems, ZR8Site/ZR8DataA, assume agreement on
every `Ω₀`-both bond; here the bond that moves lies INSIDE `Ω₀`, far from `Ω₁`, so the proofs are redone with ball hypotheses.)
`farAgree_update`: a configuration changed at one bond based farther than `r` from `Ω₁` satisfies `FarAgree S r`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)

variable {L : PeriodicLatticeExtent}

/-- `U` and `U'` agree on every bond based within distance `r` of `Ω₁`. -/
def FarAgree (S : Tower L) (r : ℕ) (U U' : Cfg L) : Prop := ∀ y ∈ S.Om 1, AgreeAt (Ball y r) U U'

theorem FarAgree.mono {S : Tower L} {r r' : ℕ} {U U' : Cfg L} (h : FarAgree S r U U') (hr : r' ≤ r) :
    FarAgree S r' U U' := fun y hy => (h y hy).mono (Ball_mono hr)

theorem farAgree_update (S : Tower L) (r : ℕ) (U0 : Cfg L) (b : Bond L) (v : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hfar : ∀ y ∈ S.Om 1, r < pdist y b.1) : FarAgree S r (Function.update U0 b v) U0 := by
  intro y hy z hz μ
  have hne : ((z, μ) : Bond L) ≠ b := by
    intro h
    have h1 : z = b.1 := by rw [← h]
    have := hfar y hy
    rw [← h1] at this
    exact absurd hz (not_le.2 this)
  exact Function.update_of_ne hne _ _

theorem rhoT_one (ell : ℕ) : rhoT ell 1 = 4 * ell := by simp [rhoT]

/-! ## 1. site rows -/

theorem Qlev_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (8 * ell) U U')
    {j : ℕ} (hj : j ≤ 1) {y : PeriodicLatticeSite L} (hy : y ∈ (geomOf ell 1 S).Lam j) :
    Qlev (geomOf ell 1 S) U j y = Qlev (geomOf ell 1 S) U' j y := by
  ext1 f
  rw [Qlev_apply, Qlev_apply]
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0; rfl
  · have hj1' : j = 1 := by omega
    subst hj1'
    refine Qcomposite_congr (geomOf ell 1 S) hell _ 1 y ?_
    have h8 : 2 * rhoT ell 1 = 8 * ell := by rw [rhoT_one]; ring
    show AgreeAt (Ball y (2 * rhoT ell 1)) U U'
    rw [h8]
    exact h y hy.2.1

open Classical in
theorem Qpa_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (8 * ell) U U')
    (a : ℝ) : Qpa (geomOf ell 1 S) U a = Qpa (geomOf ell 1 S) U' a := by
  unfold Qpa
  refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun y _ => ?_))
  split_ifs with hy
  · have hjk : j ≤ 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Qlev_congr_far hell h hjk hy]
  · rfl

theorem NQp_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (8 * ell) U U') :
    NQp (geomOf ell 1 S) U = NQp (geomOf ell 1 S) U' := by
  ext f
  show ((∀ x, x ∉ (geomOf ell 1 S).Om0 → f x = 0) ∧ ∀ j, j ≤ (geomOf ell 1 S).k → ∀ y, y ∈ (geomOf ell 1 S).Lam j →
      Qlev (geomOf ell 1 S) U j y f = 0) ↔
    ((∀ x, x ∉ (geomOf ell 1 S).Om0 → f x = 0) ∧ ∀ j, j ≤ (geomOf ell 1 S).k → ∀ y, y ∈ (geomOf ell 1 S).Lam j →
      Qlev (geomOf ell 1 S) U' j y f = 0)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj y hy => by rw [← Qlev_congr_far hell h hj hy]; exact h2 j hj y hy⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj y hy => by rw [Qlev_congr_far hell h hj hy]; exact h2 j hj y hy⟩

/-- elements of `N(Q')` vanish off `Ω₁` (level-0 rows are the identity on `Λ₀ = Ω₀ \ Ω₁`). -/
theorem NQp_vanish {ell : ℕ} {S : Tower L} {U : Cfg L} {f : SiteL2 L} (hf : f ∈ NQp (geomOf ell 1 S) U)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 1) : f x = 0 := by
  by_cases h0 : x ∈ S.Om 0
  · have := hf.2 0 (Nat.zero_le _) x ⟨fun μ => by simp, h0, hx⟩
    rw [Qlev_apply] at this
    exact this
  · exact hf.1 x h0

/-! ## 2. gradients of fields living near `Ω₁` -/

/-- the "near `Ω₁`" support condition: `g x = 0` whenever no site of `Ω₁` is within distance `1` of `x`. -/
def NearOm1 (S : Tower L) (g : SiteL2 L) : Prop := ∀ x : PeriodicLatticeSite L, (∀ y ∈ Ball x 1, y ∉ S.Om 1) → g x = 0

theorem nearOm1_of_vanish {S : Tower L} {g : SiteL2 L} (hg : ∀ x, x ∉ S.Om 1 → g x = 0) : NearOm1 S g :=
  fun x hx => hg x (hx x (mem_Ball_self _ _))

/-- at a bond where `U` and `U'` differ, the gradient of a near-`Ω₁` field vanishes (for every configuration). -/
theorem grad_zero_of_ne {S : Tower L} {U U' : Cfg L} (h : FarAgree S 2 U U') {g : SiteL2 L} (hg : NearOm1 S g)
    {x : PeriodicLatticeSite L} {μ : Fin 3} (hne : U (x, μ) ≠ U' (x, μ)) (V : Cfg L) :
    (WithLp.ofLp (gradL2 V g)) (x, μ) = 0 := by
  rw [gradL2_apply]
  unfold gradValueCovariant
  have h1 : (WithLp.ofLp g) x = 0 := by
    refine hg x (fun y hy hyO => hne ?_)
    refine (h y hyO) x ?_ μ
    show pdist y x ≤ 2
    have : pdist x y ≤ 1 := hy
    rw [pdist_comm]; omega
  have h2 : (WithLp.ofLp g) (periodicLatticeShift x μ) = 0 := by
    refine hg _ (fun y hy hyO => hne ?_)
    refine (h y hyO) x ?_ μ
    show pdist y x ≤ 2
    have h3 : pdist (periodicLatticeShift x μ) y ≤ 1 := hy
    have h4 : pdist y x ≤ pdist y (periodicLatticeShift x μ) + pdist (periodicLatticeShift x μ) x := pdist_triangle _ _ _
    have h5 : pdist (periodicLatticeShift x μ) x ≤ 1 := by rw [pdist_comm]; exact pdist_shift_le x μ
    rw [pdist_comm y (periodicLatticeShift x μ)] at h4
    omega
  simp only [h1, h2, map_zero, sub_zero]

theorem grad_congr_near {S : Tower L} {U U' : Cfg L} (h : FarAgree S 2 U U') {g : SiteL2 L} (hg : NearOm1 S g) :
    gradL2 U g = gradL2 U' g := by
  refine PiLp.ext (fun b => ?_)
  obtain ⟨x, μ⟩ := b
  show (WithLp.ofLp (gradL2 U g)) (x, μ) = (WithLp.ofLp (gradL2 U' g)) (x, μ)
  by_cases hb : U (x, μ) = U' (x, μ)
  · rw [gradL2_apply, gradL2_apply]
    unfold gradValueCovariant
    rw [hb]
  · rw [grad_zero_of_ne h hg hb U, grad_zero_of_ne h hg hb U']

theorem lapFull_congr_near {S : Tower L} {U U' : Cfg L} (h : FarAgree S 2 U U') {g : SiteL2 L} (hg : NearOm1 S g) :
    lapFull U g = lapFull U' g := by
  refine ext_inner_left ℝ (fun k => ?_)
  simp only [lapFull, gradAdj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  obtain ⟨x, μ⟩ := b
  by_cases hb : U (x, μ) = U' (x, μ)
  · show inner ℝ ((WithLp.ofLp (gradL2 U k)) (x, μ)) ((WithLp.ofLp (gradL2 U g)) (x, μ))
      = inner ℝ ((WithLp.ofLp (gradL2 U' k)) (x, μ)) ((WithLp.ofLp (gradL2 U' g)) (x, μ))
    rw [gradL2_apply, gradL2_apply, gradL2_apply, gradL2_apply]
    unfold gradValueCovariant
    rw [hb]
  · show inner ℝ ((WithLp.ofLp (gradL2 U k)) (x, μ)) ((WithLp.ofLp (gradL2 U g)) (x, μ))
      = inner ℝ ((WithLp.ofLp (gradL2 U' k)) (x, μ)) ((WithLp.ofLp (gradL2 U' g)) (x, μ))
    rw [grad_zero_of_ne h hg hb U, grad_zero_of_ne h hg hb U', inner_zero_right, inner_zero_right]

/-! ## 3. `Δ_U N(Q')`, `R`, `T = R D*` -/

theorem lapDir_congr_NQp {ell : ℕ} {S : Tower L} {U U' V : Cfg L} (h : FarAgree S 2 U U') {f : SiteL2 L}
    (hf : f ∈ NQp (geomOf ell 1 S) V) : lapDir (geomOf ell 1 S) U f = lapDir (geomOf ell 1 S) U' f := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [lapFull_congr_near h (g := siteMask (geomOf ell 1 S).Om0 f) ?_]
  refine nearOm1_of_vanish (fun x hx => ?_)
  rw [siteMask_apply]
  split_ifs
  · exact NQp_vanish hf x hx
  · rfl

theorem RImage_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (8 * ell) U U') :
    RImage (geomOf ell 1 S) U = RImage (geomOf ell 1 S) U' := by
  have h2 : FarAgree S 2 U U' := h.mono (by omega)
  unfold RImage
  rw [NQp_congr_far hell h]
  ext v
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, (lapDir_congr_NQp h2 hf).symm⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, lapDir_congr_NQp h2 hf⟩

theorem Rproj_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (8 * ell) U U') :
    Rproj (geomOf ell 1 S) U = Rproj (geomOf ell 1 S) U' := by
  unfold Rproj
  simp only [RImage_congr_far hell h]

theorem RImage_near {ell : ℕ} {S : Tower L} {U : Cfg L} {v : SiteL2 L} (hv : v ∈ RImage (geomOf ell 1 S) U) :
    NearOm1 S v :=
  fun x hx => RImage_support S U hv x hx

theorem Tfull_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (8 * ell) U U') :
    Tfull (geomOf ell 1 S) U = Tfull (geomOf ell 1 S) U' := by
  have h2 : FarAgree S 2 U U' := h.mono (by omega)
  ext1 A
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  rw [← Rproj_congr_far hell h]
  rw [← sub_eq_zero, ← map_sub]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro v hv
  rw [inner_sub_right, gradAdj, gradAdj, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right, grad_congr_near h2 (RImage_near hv), sub_self]

/-! ## 4. the bond sector and the mass term -/

theorem QfullOf_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (9 * ell) U U') :
    QfullOf (geomOf ell 1 S) U = QfullOf (geomOf ell 1 S) U' := by
  ext1 A
  refine PiLp.ext (fun p => ?_)
  obtain ⟨j, b, hb⟩ := p
  show (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell 1 S) U j A)) b
    = (((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell 1 S) U' j A)) b
  congr 1
  rw [QlinB_apply, QlinB_apply]
  refine suCoordInv_apply_congr ?_
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj1
  · rw [hj0]; rfl
  · have hj : (j : ℕ) = 1 := by have := j.isLt; simp only [geomOf] at this; omega
    rw [hj]
    refine QlinCompL_congr_U (geomOf ell 1 S) hell _ 1 b ?_
    have h8 : 2 * rhoT (geomOf ell 1 S).ell 1 = 8 * ell := by
      show 2 * rhoT ell 1 = 8 * ell
      rw [rhoT_one]; ring
    rw [h8]
    have hb1 : b ∈ bondsLam (geomOf ell 1 S) 1 := by rw [hj] at hb; exact hb
    rcases hb1.1 with hy | hy
    · exact (h b.1 hy.2.1).mono (Ball_mono (by omega))
    · refine (h _ hy.2.1).mono (Ball_sub (d := ell) ?_ (by omega))
      rw [pdist_comm]
      have := pdist_coarseShift_le b.1 ((geomOf ell 1 S).ell ^ 1) b.2
      simpa [geomOf] using this

theorem MassFull_congr_far {ell : ℕ} (hell : 0 < ell) {S : Tower L} {U U' : Cfg L} (h : FarAgree S (9 * ell) U U')
    (a : ℝ) :
    MassFull (geomOf ell 1 S) a (bondSectorOf (geomOf ell 1 S) U) =
      MassFull (geomOf ell 1 S) a (bondSectorOf (geomOf ell 1 S) U') := by
  unfold MassFull
  have : (bondSectorOf (geomOf ell 1 S) U).Qfull = (bondSectorOf (geomOf ell 1 S) U').Qfull :=
    QfullOf_congr_far hell h
  rw [this]

#print axioms farAgree_update
#print axioms Qlev_congr_far
#print axioms Qpa_congr_far
#print axioms NQp_congr_far
#print axioms NQp_vanish
#print axioms grad_congr_near
#print axioms lapFull_congr_near
#print axioms RImage_congr_far
#print axioms Rproj_congr_far
#print axioms Tfull_congr_far
#print axioms QfullOf_congr_far
#print axioms MassFull_congr_far

end AdalyFormal.CoverNec
