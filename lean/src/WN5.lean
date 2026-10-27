import WN4

/-!
# WN5 (renamed from NF5: module-name collision with deps/base/NF4) -- the bond-composite (mass) drift `δm` on the two-stratum patch

BC6 `hm_of_tower` bounds the weighted mass drift `Σ_p a ℓ^{p.1} ‖(Q(1)x)_p − (Q(U)x)_p‖²` on the FULL tower (rows at level
`k` only).  Here, for any tower `S` on `scaleUp ℓ k Lu` with the full-tower `TowerClass` and `RegTower`:
* `bondsLam_aligned` : a bond row at level `i ≤ k` has an `ℓ^i`-aligned base point.
* `mass_level_le`    : the level-`i` part is `≤ a ℓ^{-i} (r^i (S_i/r) e^{S_i/r})² ‖x‖²` (`r = ℓ^{-1/2}`,
  `S_i = Σ_{i'<i} θ(ε_{i'})`; BC5 `tower_FG` at level `i`).
* `hm_patch` : on the patch (`k = j+1`, rows at levels `j`, `j+1` only)
  `Σ_p … ≤ (√2 · ℓ · deltaM ℓ (j+1) a ε)² ‖x‖²`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

open scoped Classical

namespace AdalyFormal.W3NF

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.StatementLane (BlockClosed scaleUp Tower)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite (TowerClass nrm nrm_sq nrm_nonneg rr thetaOf thetaOf_nonneg deltaM flatBg tower_FG
  Qfull_apply_level nrm_one_suCoord suOf_sub sum_le_of_injective hdvd_scaleUp rr_sq phi_mono)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.M1Patch (patchTower lam_lt)

section level
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu))

theorem bondsLam_aligned (hell : 0 < ell) (i : ℕ) (hi : i ≤ k) (b : Bond (scaleUp ell k Lu))
    (hb : b ∈ bondsLam (geomOf ell k S) i) : b.1 ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ i) := by
  rw [mem_CoarseLattice]
  intro ν
  rcases hb.1 with h | h
  · exact Nat.mod_eq_zero_of_dvd (h.1 ν)
  · have hz := h.1 ν
    by_cases hν : ν = b.2
    · subst hν
      have hz' : ell ^ i ∣ ((b.1 b.2).val + ell ^ i) % (scaleUp ell k Lu b.2 + 1) := by
        have := hz
        rwa [show (geomOf ell k S).ell = ell from rfl, coarseShift_val_eq] at this
      have hN : ell ^ i ∣ scaleUp ell k Lu b.2 + 1 := hdvd_scaleUp ell k Lu hell i hi b.2
      have h1 := (Nat.dvd_mod_iff hN).mp hz'
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add_self_right.mp h1)
    · have := hz
      rw [show (geomOf ell k S).ell = ell from rfl, coarseShift_apply_ne b.1 (ell ^ i) b.2 ν hν] at this
      exact Nat.mod_eq_zero_of_dvd this

/-- the aligned coarse bond of a level-`i` bond row -/
def rowCB (hell : 0 < ell) (i : ℕ) (hi : i ≤ k) (b : {b // b ∈ bondsLam (geomOf ell k S) i}) :
    CoarseBond (scaleUp ell k Lu) (ell ^ i) :=
  (⟨b.1.1, bondsLam_aligned ell k Lu S hell i hi b.1 b.2⟩, b.1.2)

theorem rowCB_injective (hell : 0 < ell) (i : ℕ) (hi : i ≤ k) : Function.Injective (rowCB ell k Lu S hell i hi) := by
  rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ i) => c.1.1) h)
    (congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ i) => c.2) h)

/-- the level-`i` drift bound -/
noncomputable def lvlB (ell : ℕ) (ε : ℕ → ℝ) (i : ℕ) : ℝ :=
  (rr ell) ^ i * ((∑ i' ∈ Finset.range i, thetaOf ell (ε i')) / rr ell)
    * Real.exp ((∑ i' ∈ Finset.range i, thetaOf ell (ε i')) / rr ell)

/-- **level-`i` part of the mass drift** -/
theorem mass_level_le (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (x : BondFnL2 (scaleUp ell k Lu)) (i : Fin (k + 1)) :
    ∑ b : {b // b ∈ bondsLam (geomOf ell k S) (i : ℕ)}, a * (ell : ℝ) ^ (i : ℕ) *
        ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨i, b⟩
          - (bondSectorOf (geomOf ell k S) U).Qfull x ⟨i, b⟩‖ ^ 2
      ≤ a * ((ell : ℝ) ^ (i : ℕ))⁻¹ * (lvlB ell ε i * ‖x‖) ^ 2 := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hik : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.isLt
  have hbgflat : bgTower (geomOf ell k S) (trivialU (scaleUp ell k Lu)) = flatBg ell k Lu :=
    funext (AdalyFormal.SliceCoerc.ubarTower_trivial ell)
  have hbgU : bgTower (geomOf ell k S) U = bgTower (GF ell k Lu) U := rfl
  have hregG : RegTower (geomOf ell k S).ell (bgTower (geomOf ell k S) U) (geomOf ell k S).k := hreg
  have hreg1 : RegTower (geomOf ell k S).ell (bgTower (geomOf ell k S) (trivialU _)) (geomOf ell k S).k := by
    rw [hbgflat]; exact AdalyFormal.BondComposite.regTower_flat ell k Lu hell k
  set Z : XS (scaleUp ell k Lu) := QlinCompX ell (bgTower (GF ell k Lu) U) i (suCoord x)
      - QlinCompX ell (flatBg ell k Lu) i (suCoord x) with hZ
  set g : CoarseBond (scaleUp ell k Lu) (ell ^ (i : ℕ)) → ℝ := fun c => ‖suOf (Z (c.1.1, c.2))‖ ^ 2 with hg
  have hgn : ∀ c, 0 ≤ g c := fun c => sq_nonneg _
  have hper : ∀ b : {b // b ∈ bondsLam (geomOf ell k S) (i : ℕ)},
      a * (ell : ℝ) ^ (i : ℕ) *
        ‖(bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨i, b⟩ - (bondSectorOf (geomOf ell k S) U).Qfull x ⟨i, b⟩‖ ^ 2
      = a * ((ell : ℝ) ^ (i : ℕ))⁻¹ * g (rowCB ell k Lu S hell i hik b) := by
    intro b
    rw [Qfull_apply_level ell k Lu _ _ hreg1, Qfull_apply_level ell k Lu _ _ hregG, hbgflat]
    show a * (ell : ℝ) ^ (i : ℕ) * ‖((ell : ℝ) ^ (i : ℕ))⁻¹ • suOf (QlinCompX ell (flatBg ell k Lu) i (suCoord x) b.1)
        - ((ell : ℝ) ^ (i : ℕ))⁻¹ • suOf (QlinCompX ell (bgTower (GF ell k Lu) U) i (suCoord x) b.1)‖ ^ 2
      = a * ((ell : ℝ) ^ (i : ℕ))⁻¹ * ‖suOf (Z (b.1.1, b.1.2))‖ ^ 2
    have hn0 : ((ell : ℝ) ^ (i : ℕ)) ≠ 0 := by positivity
    have hsub : suOf (QlinCompX ell (flatBg ell k Lu) i (suCoord x) b.1)
          - suOf (QlinCompX ell (bgTower (GF ell k Lu) U) i (suCoord x) b.1)
        = - suOf (Z (b.1.1, b.1.2)) := by
      rw [hZ, Pi.sub_apply, suOf_sub]
      simp
    rw [← smul_sub, hsub, norm_smul, norm_neg, mul_pow, Real.norm_eq_abs, abs_inv,
      abs_of_pos (pow_pos hellR _), inv_pow]
    field_simp
  rw [Finset.sum_congr rfl fun b _ => hper b, ← Finset.mul_sum]
  have h1 : ∑ b : {b // b ∈ bondsLam (geomOf ell k S) (i : ℕ)}, g (rowCB ell k Lu S hell i hik b) ≤ ∑ c, g c :=
    sum_le_of_injective _ (rowCB_injective ell k Lu S hell i hik) g hgn
  have h2 : ∑ c, g c = nrm (ell ^ (i : ℕ)) Z ^ 2 := by rw [nrm_sq]
  have hFG := (tower_FG ell k Lu hell U ε hreg hcl hε0 hsm (suCoord x) i hik).2
  rw [nrm_one_suCoord] at hFG
  have h4 : nrm (ell ^ (i : ℕ)) Z ^ 2 ≤ (lvlB ell ε i * ‖x‖) ^ 2 := pow_le_pow_left₀ (nrm_nonneg _ _) hFG 2
  have hcoef : 0 ≤ a * ((ell : ℝ) ^ (i : ℕ))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (h1.trans (h2 ▸ h4)) hcoef

end level

/-- `ℓ^{-i} B_i² ≤ ℓ² deltaM²/a`-type comparison: for `j ≤ i ≤ j+1`, `a ℓ^{-i} B_i² ≤ ℓ² deltaM(j+1)²`. -/
theorem lvl_le_deltaM (ell j : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ)
    (hε0 : ∀ i, i < j + 1 → 0 ≤ ε i) (i : ℕ) (hji : j ≤ i) (hij : i ≤ j + 1) :
    a * ((ell : ℝ) ^ i)⁻¹ * lvlB ell ε i ^ 2 ≤ (ell : ℝ) ^ 2 * deltaM ell (j + 1) a ε ^ 2 := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellP : (0 : ℝ) < ell := by linarith
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  set Si := ∑ i' ∈ Finset.range i, thetaOf ell (ε i') with hSi
  set Sk := ∑ i' ∈ Finset.range (j + 1), thetaOf ell (ε i') with hSk
  have hSi0 : 0 ≤ Si := Finset.sum_nonneg (fun i' hi' => thetaOf_nonneg ell _ (hε0 i' (by
    have := Finset.mem_range.mp hi'; omega)))
  have hSik : Si ≤ Sk := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun i' hi' _ => thetaOf_nonneg ell _ (hε0 i' (Finset.mem_range.mp hi')))
  set φi := (Si / rr ell) * Real.exp (Si / rr ell) with hφi
  set φk := (Sk / rr ell) * Real.exp (Sk / rr ell) with hφk
  have hφ0 : 0 ≤ φi := by positivity
  have hφ := phi_mono (rr ell) hr hSi0 hSik
  have hrr2 := rr_sq ell hell
  -- lvlB^2 = rr^{2i} φi^2 = ℓ^{-i} φi^2
  have hB : lvlB ell ε i ^ 2 = ((ell : ℝ) ^ i)⁻¹ * φi ^ 2 := by
    unfold lvlB
    rw [← hSi]
    have : (rr ell ^ i) ^ 2 = ((ell : ℝ) ^ i)⁻¹ := by
      rw [← pow_mul, mul_comm, pow_mul, hrr2, one_div, inv_pow]
    calc (rr ell ^ i * (Si / rr ell) * Real.exp (Si / rr ell)) ^ 2 = (rr ell ^ i) ^ 2 * φi ^ 2 := by
          rw [hφi]; ring
      _ = _ := by rw [this]
  have hD : deltaM ell (j + 1) a ε ^ 2 = a * (((ell : ℝ) ^ (j + 1))⁻¹) ^ 2 * φk ^ 2 := by
    unfold deltaM
    rw [← hSk]
    have h1 : (rr ell ^ (j + 1)) ^ 2 = ((ell : ℝ) ^ (j + 1))⁻¹ := by
      rw [← pow_mul, mul_comm, pow_mul, hrr2, one_div, inv_pow]
    have h2 : Real.sqrt (a / (ell : ℝ) ^ (j + 1)) ^ 2 = a / (ell : ℝ) ^ (j + 1) :=
      Real.sq_sqrt (div_nonneg ha (by positivity))
    calc (Real.sqrt (a / (ell : ℝ) ^ (j + 1)) * (rr ell ^ (j + 1) * ((Sk / rr ell) * Real.exp (Sk / rr ell)))) ^ 2
        = Real.sqrt (a / (ell : ℝ) ^ (j + 1)) ^ 2 * (rr ell ^ (j + 1)) ^ 2 * φk ^ 2 := by rw [hφk]; ring
      _ = _ := by rw [h2, h1]; ring
  rw [hB, hD]
  have hii : ((ell : ℝ) ^ i)⁻¹ ≤ ((ell : ℝ) ^ j)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hellR hji)
  have hpow : (ell : ℝ) ^ 2 * (((ell : ℝ) ^ (j + 1))⁻¹) ^ 2 = (((ell : ℝ) ^ j)⁻¹) ^ 2 := by
    rw [pow_succ]; field_simp; ring
  have hφ2 : φi ^ 2 ≤ φk ^ 2 := pow_le_pow_left₀ hφ0 hφ 2
  have hinv0 : 0 ≤ ((ell : ℝ) ^ i)⁻¹ := by positivity
  calc a * ((ell : ℝ) ^ i)⁻¹ * (((ell : ℝ) ^ i)⁻¹ * φi ^ 2)
      = a * (((ell : ℝ) ^ i)⁻¹) ^ 2 * φi ^ 2 := by ring
    _ ≤ a * (((ell : ℝ) ^ j)⁻¹) ^ 2 * φk ^ 2 := by
        have h3 : (((ell : ℝ) ^ i)⁻¹) ^ 2 ≤ (((ell : ℝ) ^ j)⁻¹) ^ 2 := pow_le_pow_left₀ hinv0 hii 2
        have := mul_le_mul h3 hφ2 (sq_nonneg _) (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left this ha]
    _ = (ell : ℝ) ^ 2 * (a * (((ell : ℝ) ^ (j + 1))⁻¹) ^ 2 * φk ^ 2) := by rw [← hpow]; ring

/-- **mass drift on the patch** -/
theorem hm_patch (ell j : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu)))
    (U : Cfg (scaleUp ell (j + 1) Lu)) (a : ℝ) (ha : 0 ≤ a) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell (j + 1) Lu) U) (j + 1)) (hcl : TowerClass ell (j + 1) Lu U ε)
    (hε0 : ∀ i, i < j + 1 → 0 ≤ ε i) (hsm : ∀ i, i < j + 1 → rhoOf ell (ε i) < Real.pi / 2)
    (x : BondFnL2 (scaleUp ell (j + 1) Lu)) :
    ∑ p : BIdx (geomOf ell (j + 1) (patchTower j Rg)), a * ((geomOf ell (j + 1) (patchTower j Rg)).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (geomOf ell (j + 1) (patchTower j Rg)) (trivialU _)).Qfull x p
          - (bondSectorOf (geomOf ell (j + 1) (patchTower j Rg)) U).Qfull x p‖ ^ 2
      ≤ (Real.sqrt 2 * (ell : ℝ) * deltaM ell (j + 1) a ε) ^ 2 * ‖x‖ ^ 2 := by
  set G := geomOf ell (j + 1) (patchTower j Rg) with hG
  set F : Fin (j + 1 + 1) → ℝ := fun i => ∑ b : {b // b ∈ bondsLam G (i : ℕ)}, a * (ell : ℝ) ^ (i : ℕ) *
        ‖(bondSectorOf G (trivialU _)).Qfull x ⟨i, b⟩ - (bondSectorOf G U).Qfull x ⟨i, b⟩‖ ^ 2 with hF
  have hsplit : ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf G (trivialU _)).Qfull x p - (bondSectorOf G U).Qfull x p‖ ^ 2 = ∑ i, F i := by
    have h := Fintype.sum_sigma (fun p : (Σ i : Fin (G.k + 1), {b // b ∈ bondsLam G (i : ℕ)}) =>
      a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖(bondSectorOf G (trivialU _)).Qfull x p - (bondSectorOf G U).Qfull x p‖ ^ 2)
    refine (Finset.sum_congr (by rfl)
      (fun p _ => rfl)).trans (h.trans ?_)
    rfl
  rw [hsplit]
  -- levels below j are empty
  have hlow : ∀ i : Fin (j + 1 + 1), (i : ℕ) < j → F i = 0 := by
    intro i hi
    have hempty : ∀ b : {b // b ∈ bondsLam G (i : ℕ)}, False := by
      intro b
      have hL : G.Lam (i : ℕ) = ∅ := lam_lt ell j Rg hi
      rcases b.2.1 with h | h
      · rw [hL] at h; exact h
      · rw [hL] at h; exact h
    simp only [hF]
    exact Finset.sum_eq_zero (fun b _ => (hempty b).elim)
  have hlev : ∀ i : Fin (j + 1 + 1), j ≤ (i : ℕ) → F i ≤ (ell : ℝ) ^ 2 * deltaM ell (j + 1) a ε ^ 2 * ‖x‖ ^ 2 := by
    intro i hi
    have h1 := mass_level_le ell (j + 1) Lu (patchTower j Rg) hell U a ha ε hreg hcl hε0 hsm x i
    have h2 := lvl_le_deltaM ell j hell a ha ε hε0 (i : ℕ) hi (Nat.lt_succ_iff.mp i.isLt)
    calc F i ≤ a * ((ell : ℝ) ^ (i : ℕ))⁻¹ * (lvlB ell ε i * ‖x‖) ^ 2 := h1
      _ = (a * ((ell : ℝ) ^ (i : ℕ))⁻¹ * lvlB ell ε i ^ 2) * ‖x‖ ^ 2 := by ring
      _ ≤ (ell : ℝ) ^ 2 * deltaM ell (j + 1) a ε ^ 2 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hzero : ∑ i : Fin j, F i.castSucc.castSucc = 0 :=
    Finset.sum_eq_zero (fun i _ => hlow _ (by simp))
  rw [hzero, zero_add]
  have hA := hlev (Fin.last j).castSucc (by simp)
  have hB := hlev (Fin.last (j + 1)) (by simp)
  have e2 : (Real.sqrt 2 * (ell : ℝ) * deltaM ell (j + 1) a ε) ^ 2
      = 2 * ((ell : ℝ) ^ 2 * deltaM ell (j + 1) a ε ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [e2]
  linarith

#print axioms bondsLam_aligned
#print axioms rowCB_injective
#print axioms mass_level_le
#print axioms lvl_le_deltaM
#print axioms hm_patch

end AdalyFormal.W3NF
