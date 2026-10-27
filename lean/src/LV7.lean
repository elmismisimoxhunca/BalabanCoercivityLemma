import LV6

/-!
# LV7 -- the exact identity `S + ℓ² Bg = Dev + Loc` on the two-stratum patch

For a site field `φ` and a divergence-free bond field `c` (flat `U`), with `Φs = Phm n φ`, `ΦB = Phm N φ`,
`Fs = Fl n n c`, `FB = Fl n N c` (`n = ℓ^j`, `N = ℓ^j ℓ`):
* `Sx`  = Σ over small rows of `⟨Φs(z + n e_μ) - Φs z, Fs z μ⟩`,
* `Bx`  = Σ over big rows of `⟨ΦB(Z + N e_μ) - ΦB Z, FB Z μ⟩`,
* `Dx`  = Σ over the interfaces (block `Z ∉ Rg`, neighbour in `Rg`) of `± ℓ² ⟨(layer mean of Φs) - ΦB Z, FB⟩`,
* `Lx`  = Σ over the interface layers of `± ⟨Φs(cell) - ΦB Z, Fs(face) - FB⟩`.
`key_identity` : `Sx + ℓ² Bx = Dx + Lx` (exact).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.FlatCoercivity (eU)
open AdalyFormal.StatementLane (BlockClosed)

variable {L : PeriodicLatticeExtent}

section defs
variable (ell j : ℕ) (Rg : Set (PeriodicLatticeSite L)) (φ : PeriodicLatticeSite L → SuTwo) (c : Bond L → SuTwo)

open Classical in
noncomputable def Sx : ℝ :=
  ∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j),
    (if z ∉ Rg ∧ z + ell ^ j • eU L μ ∉ Rg then
      ⟪Phm (ell ^ j) φ (z + ell ^ j • eU L μ) - Phm (ell ^ j) φ z, Fl (ell ^ j) (ell ^ j) c z μ⟫ else 0)

open Classical in
noncomputable def Bx : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell),
    (if Z ∈ Rg ∨ Z + (ell ^ j * ell) • eU L μ ∈ Rg then
      ⟪Phm (ell ^ j * ell) φ (Z + (ell ^ j * ell) • eU L μ) - Phm (ell ^ j * ell) φ Z,
        Fl (ell ^ j) (ell ^ j * ell) c Z μ⟫ else 0)

/-- layer means -/
noncomputable def Ptop (Z : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (((ell : ℝ) ^ 2)⁻¹) • ∑ k ∈ face ell μ, Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ)

noncomputable def Pbot (Z : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (((ell : ℝ) ^ 2)⁻¹) • ∑ k ∈ face ell μ, Phm (ell ^ j) φ (bz (ell ^ j) Z k)

open Classical in
noncomputable def Dx : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell),
    (if Z ∉ Rg then
      ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          (ell : ℝ) ^ 2 * ⟪Ptop ell j φ Z μ - Phm (ell ^ j * ell) φ Z, Fl (ell ^ j) (ell ^ j * ell) c Z μ⟫ else 0)
        - (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
          (ell : ℝ) ^ 2 * ⟪Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z,
            Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ⟫ else 0)) else 0)

open Classical in
noncomputable def Lx : ℝ :=
  ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell),
    (if Z ∉ Rg then
      ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ) - Phm (ell ^ j * ell) φ Z,
            Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ - Fl (ell ^ j) (ell ^ j * ell) c Z μ⟫ else 0)
        - (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
          ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z,
            Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
              - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ⟫ else 0)) else 0)

end defs

theorem tz_eq (n ℓ : ℕ) (Z : PeriodicLatticeSite L) (k : Fin 3 → ℕ) (μ : Fin 3) (hk : k ∈ face ℓ μ) :
    Z + off L (n • Function.update k μ (ℓ - 1)) = tz n ℓ Z k μ := by
  have hk0 : k μ = 0 := ((mem_face ℓ μ k).mp hk).2
  have hk' : Function.update k μ 0 = k := by
    funext ν; by_cases hν : ν = μ
    · subst hν; simp [hk0]
    · simp [Function.update_of_ne hν]
  have h := off_smul_update (L := L) n (Function.update k μ (ℓ - 1)) μ 0
  rw [Function.update_idem, Function.update_self, hk'] at h
  unfold tz
  rw [h]
  simp only [mul_zero, zero_smul, sub_zero]
  abel

theorem bz_eq (n ℓ : ℕ) (Z : PeriodicLatticeSite L) (k : Fin 3 → ℕ) (μ : Fin 3) (hk : k ∈ face ℓ μ) :
    Z + off L (n • Function.update k μ 0) = bz n Z k := by
  have hk0 : k μ = 0 := ((mem_face ℓ μ k).mp hk).2
  have : Function.update k μ 0 = k := by
    funext ν; by_cases hν : ν = μ
    · subst hν; simp [hk0]
    · simp [Function.update_of_ne hν]
  rw [this]; rfl

theorem tz_down (n ℓ : ℕ) (hℓ : 0 < ℓ) (Z : PeriodicLatticeSite L) (k : Fin 3 → ℕ) (μ : Fin 3) :
    tz n ℓ (Z - (n * ℓ) • eU L μ) k μ = bz n Z k - n • eU L μ := by
  unfold tz bz
  have : n * ℓ = n * (ℓ - 1) + n := by
    obtain ⟨e', he'⟩ : ∃ e', ℓ = e' + 1 := ⟨ℓ - 1, by omega⟩
    rw [he', Nat.add_sub_cancel]; ring
  rw [this, add_nsmul]
  abel

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

theorem hdn : ∀ μ : Fin 3, ell ^ j ∣ L μ + 1 := fun μ => (pow_dvd_pow ell (Nat.le_succ j)).trans (hdvd μ)

open Classical in
/-- the small-row boundary terms regrouped by big blocks. -/
theorem small_regroup (X Y : PeriodicLatticeSite L → Fin 3 → ℝ) :
    ∑ μ : Fin 3, ∑ z ∈ latF L (ell ^ j),
      (if z ∉ Rg then ((if z + ell ^ j • eU L μ ∈ Rg then X z μ else 0)
        - (if z - ell ^ j • eU L μ ∈ Rg then Y z μ else 0)) else 0)
    = ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell),
      (if Z ∉ Rg then ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ, X (tz (ell ^ j) ell Z k μ) μ else 0)
        - (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ, Y (bz (ell ^ j) Z k) μ else 0)) else 0) := by
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [regroup hell hdvd]
  refine Finset.sum_congr rfl (fun Z hZ => ?_)
  rw [mem_latF] at hZ
  by_cases hZR : Z ∈ Rg
  · rw [if_neg (not_not.mpr hZR)]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [if_neg (not_not.mpr ((cell_Rg hell hRg hdvd Z hZ i hi).mpr hZR))]
  · rw [if_pos hZR]
    have hpt : ∀ i ∈ cube ell,
        (if Z + off L (ell ^ j • i) ∉ Rg then
          ((if Z + off L (ell ^ j • i) + ell ^ j • eU L μ ∈ Rg then X (Z + off L (ell ^ j • i)) μ else 0)
            - (if Z + off L (ell ^ j • i) - ell ^ j • eU L μ ∈ Rg then Y (Z + off L (ell ^ j • i)) μ else 0)) else 0)
        = (if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
              (if i μ = ell - 1 then X (Z + off L (ell ^ j • i)) μ else 0) else 0)
          - (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
              (if i μ = 0 then Y (Z + off L (ell ^ j • i)) μ else 0) else 0) := by
      intro i hi
      rw [if_pos (fun h => hZR ((cell_Rg hell hRg hdvd Z hZ i hi).mp h))]
      rw [up_Rg hell hRg hdvd Z hZ hZR i hi μ, down_Rg hell hRg hdvd Z hZ hZR i hi μ]
      by_cases h1 : i μ = ell - 1 <;> by_cases h2 : Z + (ell ^ j * ell) • eU L μ ∈ Rg <;>
        by_cases h3 : i μ = 0 <;> by_cases h4 : Z - (ell ^ j * ell) • eU L μ ∈ Rg <;> simp [h1, h2, h3, h4]
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
    congr 1
    · by_cases h2 : Z + (ell ^ j * ell) • eU L μ ∈ Rg
      · simp only [h2, if_true]
        rw [cube_layer ell μ (ell - 1) (by omega)]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [tz_eq (ell ^ j) ell Z k μ hk]
      · simp [h2]
    · by_cases h4 : Z - (ell ^ j * ell) • eU L μ ∈ Rg
      · simp only [h4, if_true]
        rw [cube_layer ell μ 0 hell]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [bz_eq (ell ^ j) ell Z k μ hk]
      · simp [h4]

/-- **the exact identity** `Sx + ℓ² Bx = Dx + Lx`. -/
theorem key_identity (φ : PeriodicLatticeSite L → SuTwo) (c : BondFnL2 L) (hc : gradAdj (flatCfg : Cfg L) c = 0) :
    Sx ell j Rg φ c.ofLp + (ell : ℝ) ^ 2 * Bx ell j Rg φ c.ofLp = Dx ell j Rg φ c.ofLp + Lx ell j Rg φ c.ofLp := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hN : 0 < ell ^ j * ell := Nat.mul_pos hn hell
  have hdN : ∀ μ : Fin 3, ell ^ j * ell ∣ L μ + 1 := hdvd
  have hdn' := hdn hell hRg hdvd
  -- small rows by parts, then regrouped
  have hS := parts_small hdn' Rg (Phm (ell ^ j) φ) (fun z μ => Fl (ell ^ j) (ell ^ j) c.ofLp z μ)
    (fun z => Fl_cons c hc (ell ^ j) (ell ^ j) hn z)
  have hS2 := small_regroup hell hRg hdvd
    (fun z μ => ⟪Phm (ell ^ j) φ z, Fl (ell ^ j) (ell ^ j) c.ofLp z μ⟫)
    (fun z μ => ⟪Phm (ell ^ j) φ z, Fl (ell ^ j) (ell ^ j) c.ofLp (z - ell ^ j • eU L μ) μ⟫)
  have hB := parts_big hdN Rg (Phm (ell ^ j * ell) φ) (fun Z μ => Fl (ell ^ j) (ell ^ j * ell) c.ofLp Z μ)
    (fun Z => Fl_cons c hc (ell ^ j) (ell ^ j * ell) hN Z)
  unfold Sx Bx Dx Lx
  simp only at hS hS2 hB
  rw [hS, hS2, hB, Finset.mul_sum]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun Z _ => ?_))
  by_cases hZR : Z ∈ Rg
  · simp [hZR]
  · simp only [hZR, not_false_eq_true, if_true]
    -- top
    have htop : (if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ),
            Fl (ell ^ j) (ell ^ j) c.ofLp (tz (ell ^ j) ell Z k μ) μ⟫ else 0)
        - (ell : ℝ) ^ 2 * (if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ⟪Phm (ell ^ j * ell) φ Z, Fl (ell ^ j) (ell ^ j * ell) c.ofLp Z μ⟫ else 0)
        = (if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
            (ell : ℝ) ^ 2 * ⟪Ptop ell j φ Z μ - Phm (ell ^ j * ell) φ Z, Fl (ell ^ j) (ell ^ j * ell) c.ofLp Z μ⟫
            else 0)
          + (if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
            ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ) - Phm (ell ^ j * ell) φ Z,
              Fl (ell ^ j) (ell ^ j) c.ofLp (tz (ell ^ j) ell Z k μ) μ - Fl (ell ^ j) (ell ^ j * ell) c.ofLp Z μ⟫
            else 0) := by
      by_cases h2 : Z + (ell ^ j * ell) • eU L μ ∈ Rg
      · simp only [h2, if_true]
        have hrel := face_rel c.ofLp (ell ^ j) ell hn hell Z μ
        have hK : ((face ell μ).card : ℝ) = (ell : ℝ) ^ 2 := card_face_real ell hell μ
        have hF : ∑ k ∈ face ell μ, Fl (ell ^ j) (ell ^ j) c.ofLp (tz (ell ^ j) ell Z k μ) μ
            = ((ell : ℝ) ^ 2) • Fl (ell ^ j) (ell ^ j * ell) c.ofLp Z μ := by
          rw [hrel, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
        have := layer_alg (face ell μ) (fun k => Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ))
          (fun k => Fl (ell ^ j) (ell ^ j) c.ofLp (tz (ell ^ j) ell Z k μ) μ)
          (Phm (ell ^ j * ell) φ Z) (Fl (ell ^ j) (ell ^ j * ell) c.ofLp Z μ) ((ell : ℝ) ^ 2)
          (by positivity) hK hF
        rw [this]
        rfl
      · simp [h2]
    have hbot : -(if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
          ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (bz (ell ^ j) Z k),
            Fl (ell ^ j) (ell ^ j) c.ofLp (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ⟫ else 0)
        + (ell : ℝ) ^ 2 * (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
          ⟪Phm (ell ^ j * ell) φ Z, Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ⟫ else 0)
        = -(if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
            (ell : ℝ) ^ 2 * ⟪Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z,
              Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ⟫ else 0)
          - (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
            ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z,
              Fl (ell ^ j) (ell ^ j) c.ofLp (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
                - Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ⟫ else 0) := by
      by_cases h4 : Z - (ell ^ j * ell) • eU L μ ∈ Rg
      · simp only [h4, if_true]
        have hrel := face_rel c.ofLp (ell ^ j) ell hn hell (Z - (ell ^ j * ell) • eU L μ) μ
        simp only [tz_down (ell ^ j) ell hell Z] at hrel
        have hK : ((face ell μ).card : ℝ) = (ell : ℝ) ^ 2 := card_face_real ell hell μ
        have hF : ∑ k ∈ face ell μ, Fl (ell ^ j) (ell ^ j) c.ofLp (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
            = ((ell : ℝ) ^ 2) • Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ := by
          rw [hrel, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
        have := layer_alg (face ell μ) (fun k => Phm (ell ^ j) φ (bz (ell ^ j) Z k))
          (fun k => Fl (ell ^ j) (ell ^ j) c.ofLp (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ)
          (Phm (ell ^ j * ell) φ Z) (Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ)
          ((ell : ℝ) ^ 2) (by positivity) hK hF
        have e2 : ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (bz (ell ^ j) Z k),
            Fl (ell ^ j) (ell ^ j) c.ofLp (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ⟫
            = (ell : ℝ) ^ 2 * ⟪Phm (ell ^ j * ell) φ Z,
                Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ⟫
              + ((ell : ℝ) ^ 2 * ⟪Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z,
                Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ⟫
              + ∑ k ∈ face ell μ, ⟪Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z,
                Fl (ell ^ j) (ell ^ j) c.ofLp (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
                  - Fl (ell ^ j) (ell ^ j * ell) c.ofLp (Z - (ell ^ j * ell) • eU L μ) μ⟫) := by
          unfold Pbot; linear_combination this
        rw [e2]; ring
      · simp [h4]
    linear_combination htop + hbot

#print axioms tz_eq
#print axioms bz_eq
#print axioms tz_down
#print axioms hdn
#print axioms small_regroup
#print axioms key_identity

end patch

end AdalyFormal.LemIFlat
