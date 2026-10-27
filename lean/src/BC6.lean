import BC5

/-!
# BC6 -- `hm` (the bond-composite drift premise `δm` of `ginv_coercive_FE_named2`) from the tower class

`hm_of_tower`: for `ε` a tower-class link bound on the blocked backgrounds (`TowerClass`), with `RegTower` (the chain's
existing premise) and `rhoOf ell (ε j) < π/2`,
  `Σ_p a ell^{p.1} ‖(Q_1 x - Q_U x) p‖² ≤ δm² ‖x‖²`,  `δm = sqrt(a/ell^k) · r^k · (S/r) · e^{S/r}`,
  `r = ell^{-1/2}`, `S = Σ_{i<k} θ(ε_i)`, `θ(ε) = ell (√192 ell ε + √240 κ(ε))`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.BondComposite

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

theorem suOf_suCoord {L : PeriodicLatticeExtent} (x : BondFnL2 L) (e : PeriodicLatticeEdge L) :
    suOf (suCoord x e) = x e :=
  Subtype.ext (toM2_fromM2 (x e).2)

theorem nrm_one_suCoord {L : PeriodicLatticeExtent} (x : BondFnL2 L) : nrm 1 (suCoord x) = ‖x‖ := by
  have h1 : nrm 1 (suCoord x) ^ 2 = ‖x‖ ^ 2 := by
    rw [nrm_sq, ← sum_edge_eq_coarse1 (fun e => ‖suOf (suCoord x e)‖ ^ 2)]
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun e _ => by rw [suOf_suCoord]
  exact le_antisymm (le_of_sq_le' (norm_nonneg _) h1.le) (le_of_sq_le' (nrm_nonneg _ _) h1.ge)

theorem bidx_level (p : BIdx (GF ell k Lu)) : (p.1 : ℕ) = k := by
  by_contra h
  have hlt : (p.1 : ℕ) < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp p.1.isLt) h
  have hLam : (GF ell k Lu).Lam (p.1 : ℕ) = ∅ := fullTower_lam_lt ell k Lu (p.1 : ℕ) hlt
  have hb : p.2.1.1 ∈ (GF ell k Lu).Lam (p.1 : ℕ) ∨
      coarseShift p.2.1.1 ((GF ell k Lu).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (GF ell k Lu).Lam (p.1 : ℕ) := p.2.2.1
  rcases hb with hb | hb
  · rw [hLam] at hb; exact hb
  · rw [hLam] at hb; exact hb

/-- a bond with at least one endpoint in `Λ_k` (aligned at `ell^k`) has its base point aligned, since
`ell^k` divides the torus side. -/
theorem aligned_of_touching (hell : 0 < ell) (y : PeriodicLatticeSite (scaleUp ell k Lu)) (μ : Fin 3)
    (h : y ∈ (GF ell k Lu).Lam k ∨ coarseShift y (ell ^ k) μ ∈ (GF ell k Lu).Lam k) :
    y ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
  rw [mem_CoarseLattice]
  intro ν
  rcases h with h | h
  · exact Nat.mod_eq_zero_of_dvd ((fullTower_lam_k ell k Lu y).mp h ν)
  · have hz := (fullTower_lam_k ell k Lu _).mp h ν
    by_cases hν : ν = μ
    · subst hν
      rw [coarseShift_val_eq] at hz
      have hN : ell ^ k ∣ scaleUp ell k Lu ν + 1 := hdvd_scaleUp ell k Lu hell k le_rfl ν
      have h1 := (Nat.dvd_mod_iff hN).mp hz
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add_self_right.mp h1)
    · rw [coarseShift_apply_ne y (ell ^ k) μ ν hν] at hz
      exact Nat.mod_eq_zero_of_dvd hz

theorem bidx_aligned (hell : 0 < ell) (p : BIdx (GF ell k Lu)) :
    p.2.1.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
  have hk := bidx_level ell k Lu p
  have hb : p.2.1.1 ∈ (GF ell k Lu).Lam (p.1 : ℕ) ∨
      coarseShift p.2.1.1 ((GF ell k Lu).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (GF ell k Lu).Lam (p.1 : ℕ) := p.2.2.1
  have key : ∀ n : ℕ, n = k →
      (p.2.1.1 ∈ (GF ell k Lu).Lam n ∨ coarseShift p.2.1.1 (ell ^ n) p.2.1.2 ∈ (GF ell k Lu).Lam n) →
      p.2.1.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ k) := by
    intro n hn h
    rw [hn] at h
    exact aligned_of_touching ell k Lu hell _ _ h
  exact key _ hk hb

/-- the aligned bond of a `BIdx` index. -/
def bidxCB (hell : 0 < ell) (p : BIdx (GF ell k Lu)) : CoarseBond (scaleUp ell k Lu) (ell ^ k) :=
  (⟨p.2.1.1, bidx_aligned ell k Lu hell p⟩, p.2.1.2)

theorem bidxCB_injective (hell : 0 < ell) : Function.Injective (bidxCB ell k Lu hell) := by
  rintro ⟨j, ⟨b, hb⟩⟩ ⟨j', ⟨b', hb'⟩⟩ h
  have hj : j = j' := by
    apply Fin.ext
    have e1 := bidx_level ell k Lu ⟨j, ⟨b, hb⟩⟩
    have e2 := bidx_level ell k Lu ⟨j', ⟨b', hb'⟩⟩
    simp only at e1 e2
    omega
  subst hj
  have hbb : b = b' := Prod.ext (congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ k) => c.1.1) h)
    (congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ k) => c.2) h)
  subst hbb
  rfl

theorem sum_le_of_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (φ : α → β)
    (hφ : Function.Injective φ) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    ∑ a, g (φ a) ≤ ∑ b, g b := by
  classical
  rw [← Finset.sum_image (f := g) (s := Finset.univ) (g := φ) (fun a _ b _ h => hφ h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hg b)

-- r8 transfer: `Qfull` is built on the LOCAL jet `QlinCompL`; the r7 form holds on a regular tower (bridge
-- `QlinCompL_eq_QlinCompX`), so the hypothesis `hreg` is added (both call sites below have it).
theorem Qfull_apply_level (G : TowerGeom (scaleUp ell k Lu)) (V : Cfg (scaleUp ell k Lu))
    (hreg : RegTower G.ell (bgTower G V) G.k) (x : BondFnL2 (scaleUp ell k Lu))
    (p : BIdx G) :
    (bondSectorOf G V).Qfull x p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (QlinCompX G.ell (bgTower G V) p.1 (suCoord x) p.2.1) := by
  have hj : (p.1 : ℕ) ≤ G.k := Nat.lt_succ_iff.mp p.1.isLt
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • suOf (QlinCompL G.ell (bgTower G V) p.1 (suCoord x) p.2.1) = _
  rw [QlinCompL_eq_QlinCompX G.ell (bgTower G V) G.k hreg p.1 hj]

/-- the explicit `δm`. -/
def deltaM (ell k : ℕ) (a : ℝ) (ε : ℕ → ℝ) : ℝ :=
  Real.sqrt (a / (ell : ℝ) ^ k) *
    ((rr ell) ^ k * (((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)
      * Real.exp ((∑ i ∈ Finset.range k, thetaOf ell (ε i)) / rr ell)))

theorem hm_of_tower (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
      ≤ deltaM ell k a ε ^ 2 * ‖x‖ ^ 2 := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hbgflat : bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu)) = flatBg ell k Lu :=
    funext (AdalyFormal.SliceCoerc.ubarTower_trivial ell)
  set Z : XS (scaleUp ell k Lu) := QlinCompX ell (bgTower (GF ell k Lu) U) k (suCoord x)
      - QlinCompX ell (flatBg ell k Lu) k (suCoord x) with hZ
  set g : CoarseBond (scaleUp ell k Lu) (ell ^ k) → ℝ := fun c => ‖suOf (Z (c.1.1, c.2))‖ ^ 2 with hg
  have hgn : ∀ c, 0 ≤ g c := fun c => sq_nonneg _
  -- the level identity (generalised level `n = k`, so no dependent rewriting)
  have key : ∀ n : ℕ, n = k → ∀ b : Bond (scaleUp ell k Lu),
      a * (ell : ℝ) ^ n * ‖((ell : ℝ) ^ n)⁻¹ • suOf (QlinCompX ell (flatBg ell k Lu) n (suCoord x) b)
          - ((ell : ℝ) ^ n)⁻¹ • suOf (QlinCompX ell (bgTower (GF ell k Lu) U) n (suCoord x) b)‖ ^ 2
        = a * ((ell : ℝ) ^ k)⁻¹ * ‖suOf (Z (b.1, b.2))‖ ^ 2 := by
    intro n hn b
    rw [hn]
    have hn0 : ((ell : ℝ) ^ k) ≠ 0 := by positivity
    have hsub : suOf (QlinCompX ell (flatBg ell k Lu) k (suCoord x) b)
          - suOf (QlinCompX ell (bgTower (GF ell k Lu) U) k (suCoord x) b)
        = - suOf (Z (b.1, b.2)) := by
      rw [hZ, Pi.sub_apply, suOf_sub]
      simp
    rw [← smul_sub, hsub, norm_smul, norm_neg, mul_pow, Real.norm_eq_abs, abs_inv,
      abs_of_pos (pow_pos hellR k), inv_pow]
    field_simp
  have hper : ∀ p : BIdx (GF ell k Lu),
      a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
      = a * ((ell : ℝ) ^ k)⁻¹ * g (bidxCB ell k Lu hell p) := by
    intro p
    have hregflat : RegTower (GF ell k Lu).ell (bgTower (GF ell k Lu) (trivialU (scaleUp ell k Lu))) (GF ell k Lu).k := by
      rw [hbgflat]; exact regTower_flat ell k Lu hell k
    rw [Qfull_apply_level ell k Lu _ _ hregflat, Qfull_apply_level ell k Lu _ _ hreg, hbgflat]
    exact key (p.1 : ℕ) (bidx_level ell k Lu p) p.2.1
  rw [Finset.sum_congr rfl fun p _ => hper p, ← Finset.mul_sum]
  have h1 : ∑ p : BIdx (GF ell k Lu), g (bidxCB ell k Lu hell p) ≤ ∑ c, g c :=
    sum_le_of_injective _ (bidxCB_injective ell k Lu hell) g hgn
  have h2 : ∑ c, g c = nrm (ell ^ k) Z ^ 2 := by rw [nrm_sq]
  have hFG := (tower_FG ell k Lu hell U ε hreg hcl hε0 hsm (suCoord x) k le_rfl).2
  rw [nrm_one_suCoord] at hFG
  set S := ∑ i ∈ Finset.range k, thetaOf ell (ε i) with hS
  have hB0 : 0 ≤ (rr ell) ^ k * ((S / rr ell) * Real.exp (S / rr ell)) := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i hi => thetaOf_nonneg ell _ (hε0 i (Finset.mem_range.mp hi))
    have : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
    positivity
  have h3 : nrm (ell ^ k) Z ≤ (rr ell) ^ k * ((S / rr ell) * Real.exp (S / rr ell)) * ‖x‖ := by
    refine hFG.trans (le_of_eq ?_)
    ring
  have h4 : nrm (ell ^ k) Z ^ 2 ≤ ((rr ell) ^ k * ((S / rr ell) * Real.exp (S / rr ell)) * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (nrm_nonneg _ _) h3 2
  have hcoef : 0 ≤ a * ((ell : ℝ) ^ k)⁻¹ := by positivity
  calc a * ((ell : ℝ) ^ k)⁻¹ * ∑ p : BIdx (GF ell k Lu), g (bidxCB ell k Lu hell p)
      ≤ a * ((ell : ℝ) ^ k)⁻¹ * ((rr ell) ^ k * ((S / rr ell) * Real.exp (S / rr ell)) * ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (h1.trans (h2 ▸ h4)) hcoef
    _ = deltaM ell k a ε ^ 2 * ‖x‖ ^ 2 := by
        have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
        have hdm : deltaM ell k a ε
            = Real.sqrt (a / (ell : ℝ) ^ k) * ((rr ell) ^ k * ((S / rr ell) * Real.exp (S / rr ell))) := rfl
        have e2 : (Real.sqrt (a / (ell : ℝ) ^ k) * ((rr ell) ^ k * ((S / rr ell) * Real.exp (S / rr ell)))) ^ 2
            = a / (ell : ℝ) ^ k * ((rr ell) ^ k * ((S / rr ell) * Real.exp (S / rr ell))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (div_nonneg ha hn.le)]
        rw [hdm, e2]
        ring

#print axioms nrm_one_suCoord
#print axioms bidx_level
#print axioms aligned_of_touching
#print axioms bidxCB_injective
#print axioms hm_of_tower

end AdalyFormal.BondComposite
