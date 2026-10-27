import UW8

/-!
# UW9 -- **the clause-2 stacking step** `stack2` (lane unif_20261016)

Old chart `Go` on `O = SlabS σ lo hi c0 c` (clauses 1, 2 at `o1, o2`), new chart `Gn` on `N = SlabS σ lo hi c ch`
(`n1, n2`), plaquette bound `η` on `O ∪ N`, `c0 + 2 ≤ c`, `c + 2 ≤ ch`, `o1 + n1 ≤ 2`, integer scale `w ≥ 1`.
The gauge `Gst = cay(Fz) · G0` on `N` and `Go` on `O` is a chart on `O ∪ N` with clause 1 at `T1st` and clause 2 at `T2st`
(explicit, below).  Nothing depends on the sizes of `O`, `N` or on `M`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open Matrix
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (frobNorm_sub_le' frobNorm_sub_comm frobNorm_su2_mul frobNorm_mul_su2 gauge_step_one
  gauge_step_two cay cay_zero cay_second4 frobNorm_cay_sub_le frobNorm_mul_le frobNorm_su2_mul_star frobNorm_mul_su2_star
  frobNorm_add3_le)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul IsSu2)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

noncomputable def Cy1c (o1 o2 n1 n2 η : ℝ) (w : ℕ) : ℝ := (9 / 2) * F1c o1 o2 n1 n2 η w
noncomputable def Cy2c (o1 o2 n1 n2 η : ℝ) (w : ℕ) : ℝ :=
  (9 / 2) * F2c o1 o2 n1 n2 η w + (27 / 4) * (2 * F1c o1 o2 n1 n2 η w) * F1c o1 o2 n1 n2 η w
noncomputable def T1st (o1 o2 n1 n2 η : ℝ) (w : ℕ) : ℝ := o1 + g01c o1 n1 η + Cy1c o1 o2 n1 n2 η w
noncomputable def T2st (o1 o2 n1 n2 η : ℝ) (w : ℕ) : ℝ :=
  o2 + (η + o2 + 2 * o1 * o1) + (g02c o1 o2 n1 n2 η + g01c o1 n1 η * (2 * Cy1c o1 o2 n1 n2 η w)
    + Cy1c o1 o2 n1 n2 η w * Cy1c o1 o2 n1 n2 η w + Cy2c o1 o2 n1 n2 η w)

/-- the glued gauge. -/
noncomputable def Gst (W : Z3 → Fin 3 → SU2) (σ τ₁ τ₂ : Fin 3) (c ch : ℤ) (lo hi : Z3) (Go Gn : Z3 → SU2) (w : ℕ) :
    Z3 → SU2 := fun p => open Classical in
  if p ∈ SlabS σ lo hi c ch then cay (Fz W σ τ₁ τ₂ c lo hi Go Gn w p) * G0 W σ c Go Gn p else Go p

theorem su2_cross_bound (A H X A' : SU2) :
    frobNorm (((A⁻¹ * H * X * A' : SU2) : M2) - (X : M2))
      ≤ frobNorm ((H : M2) - 1) + frobNorm ((A' : M2) - A) + 2 * frobNorm ((X : M2) - 1) * frobNorm ((A : M2) - 1) := by
  have hc := comm_bound X A
  simp only [coe_mul, coe_inv] at hc ⊢
  have hA := AdalyFormal.M2Glue2.su2_star_mul A
  have e : (A : M2)ᴴ * H * X * A' - X
      = (A : M2)ᴴ * ((H : M2) - 1) * X * A' + (A : M2)ᴴ * X * ((A' : M2) - A) + (A : M2)ᴴ * ((X : M2) * A - A * X) := by
    have e2 : (A : M2)ᴴ * ((X : M2) * A - A * X) = (A : M2)ᴴ * X * A - (A : M2)ᴴ * A * X := by noncomm_ring
    rw [e2, hA]; noncomm_ring
  rw [e]
  refine (frobNorm_add3_le _ _ _).trans ?_
  have a : frobNorm ((A : M2)ᴴ * ((H : M2) - 1) * X * A') = frobNorm ((H : M2) - 1) := by
    rw [frobNorm_mul_su2, frobNorm_mul_su2, frobNorm_su2_mul_star]
  have b : frobNorm ((A : M2)ᴴ * X * ((A' : M2) - A)) = frobNorm ((A' : M2) - A) := by
    rw [mul_assoc, frobNorm_su2_mul_star, frobNorm_su2_mul]
  have c : frobNorm ((A : M2)ᴴ * ((X : M2) * A - A * X)) = frobNorm ((X : M2) * A - A * X) := frobNorm_su2_mul_star _ _
  linarith

theorem memO {σ : Fin 3} {lo hi : Z3} {c0 c ch : ℤ} {p : Z3} (hp : p ∈ SlabS σ lo hi c0 ch) (h : p σ < c) : p ∈ SlabS σ lo hi c0 c := ⟨hp.1, hp.2.1, h⟩
theorem memN {σ : Fin 3} {lo hi : Z3} {c0 c ch : ℤ} {p : Z3} (hp : p ∈ SlabS σ lo hi c0 ch) (h : c ≤ p σ) : p ∈ SlabS σ lo hi c ch := ⟨hp.1, h, hp.2.2⟩

section main
variable {W : Z3 → Fin 3 → SU2} {σ τ₁ τ₂ : Fin 3} {lo hi : Z3} {c0 c ch : ℤ} {Go Gn : Z3 → SU2} {w : ℕ}
  (hc0 : c0 + 2 ≤ c) (hch : c + 2 ≤ ch)
  {o1 o2 n1 n2 η : ℝ}
  (hO1 : C1 W Go (SlabS σ lo hi c0 c) o1) (hO2 : C2 W Go (SlabS σ lo hi c0 c) o2)
  (hN1 : C1 W Gn (SlabS σ lo hi c ch) n1) (hN2 : C2 W Gn (SlabS σ lo hi c ch) n2)
  (hH : HolB W (SlabS σ lo hi c0 ch) η)
  (ho1 : 0 ≤ o1) (hn1 : 0 ≤ n1) (hη : 0 ≤ η) (ho2 : 0 ≤ o2) (hn2 : 0 ≤ n2) (hsm : o1 + n1 ≤ 2)
  (hlh : ∀ ν, ν ≠ σ → lo ν ≤ hi ν) (hτ : ∀ ν, ν ≠ σ → ν = τ₁ ∨ ν = τ₂) (h1σ : τ₁ ≠ σ) (h2σ : τ₂ ≠ σ) (hw : 1 ≤ w)
include hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw


theorem gst_O {p : Z3} (hp : p ∈ SlabS σ lo hi c0 c) : Gst W σ τ₁ τ₂ c ch lo hi Go Gn w p = Go p := by
  have : p ∉ SlabS σ lo hi c ch := fun h => by have := h.2.1; have := hp.2.2; omega
  simp [Gst, this]

theorem gst_N {p : Z3} (hp : p ∈ SlabS σ lo hi c ch) :
    Gst W σ τ₁ τ₂ c ch lo hi Go Gn w p = cay (Fz W σ τ₁ τ₂ c lo hi Go Gn w p) * G0 W σ c Go Gn p := by
  simp [Gst, hp]

/-- the bond inside `N`. -/
theorem gst_bond_N {p : Z3} {ν : Fin 3} (hp : p ∈ SlabS σ lo hi c ch) (hpν : p + ev ν ∈ SlabS σ lo hi c ch) :
    gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) p ν
      = cay (Fz W σ τ₁ τ₂ c lo hi Go Gn w p) * gt W (G0 W σ c Go Gn) p ν
        * (cay (Fz W σ τ₁ τ₂ c lo hi Go Gn w (p + ev ν)))⁻¹ := by
  rw [← gt_mul W (fun q => cay (Fz W σ τ₁ τ₂ c lo hi Go Gn w q)) (G0 W σ c Go Gn) p ν]
  exact gt_congr (gst_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hp)
    (gst_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hpν)

/-- the crossing bond equals the bond two layers below. -/
theorem gst_cross {q : Z3} (hq : q ∈ SlabS σ lo hi c0 c) (hqN : q + ev σ ∈ SlabS σ lo hi c ch) :
    gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) q σ = Az W σ Go (q + ev σ) := by
  have hpl : (q + ev σ) σ = c := by have := hq.2.2; have := hqN.2.1; simp [ev_apply_self] at *; omega
  simp only [gt]
  rw [gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hq,
    gst_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hqN,
    fz_plane hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hpl, cay_zero, one_mul,
    g0_plane_val W σ c Go Gn hpl, show q + ev σ - ev σ = q by abel]
  group

/-- `Az` differences along a transverse direction. -/
theorem az_diff {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) {μ : Fin 3} (hμ : μ ≠ σ)
    (hxμ : x + ev μ ∈ SlabS σ lo hi c ch) :
    frobNorm (((Az W σ Go (x + ev μ) : SU2) : M2) - ((Az W σ Go x : SU2) : M2)) ≤ o2 := by
  have l := plane_below σ lo hi c0 c ch hc0 (by omega) hx hxc
  have lμ := plane_below σ lo hi c0 c ch hc0 (by omega) hxμ (by simp [ev_apply_ne (Ne.symm hμ), hxc])
  have := hO2 (x - ev σ - ev σ) μ σ l.2 (by rw [show x - ev σ - ev σ + ev σ = x - ev σ by abel]; exact l.1)
    (by rw [show x - ev σ - ev σ + ev μ = x + ev μ - ev σ - ev σ by abel]; exact lμ.2)
    (by rw [show x - ev σ - ev σ + ev μ + ev σ = x + ev μ - ev σ by abel]; exact lμ.1)
  simp only [Az]; rw [show x + ev μ - ev σ - ev σ = x - ev σ - ev σ + ev μ by abel]; exact this

theorem nonnegs : 0 ≤ K0c o1 n1 η ∧ 0 ≤ g01c o1 n1 η ∧ 0 ≤ g02c o1 o2 n1 n2 η ∧ 0 ≤ VBc o1 n1 ∧
    0 ≤ Dvc o1 o2 n1 n2 η ∧ 0 ≤ F1c o1 o2 n1 n2 η w ∧ 0 ≤ F2c o1 o2 n1 n2 η w ∧
    0 ≤ Cy1c o1 o2 n1 n2 η w ∧ 0 ≤ Cy2c o1 o2 n1 n2 η w := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have k : 0 ≤ K0c o1 n1 η := by unfold K0c; positivity
  have g1 : 0 ≤ g01c o1 n1 η := by unfold g01c; positivity
  have g2 : 0 ≤ g02c o1 o2 n1 n2 η := by unfold g02c; positivity
  have v : 0 ≤ VBc o1 n1 := by unfold VBc; positivity
  have d : 0 ≤ Dvc o1 o2 n1 n2 η := by unfold Dvc; positivity
  have f1 : 0 ≤ F1c o1 o2 n1 n2 η w := by unfold F1c; positivity
  have f2 : 0 ≤ F2c o1 o2 n1 n2 η w := by unfold F2c; positivity
  exact ⟨k, g1, g2, v, d, f1, f2, by unfold Cy1c; positivity, by unfold Cy2c; positivity⟩

/-- **clause 1 of the glued gauge.** -/
theorem stack2_c1 : C1 W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) (SlabS σ lo hi c0 ch) (T1st o1 o2 n1 n2 η w) := by
  obtain ⟨hk, hg1, hg2, hv, hd, hf1, hf2, hc1, hc2⟩ := nonnegs hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw
  intro p ν hp hpν
  have hT : T1st o1 o2 n1 n2 η w = o1 + g01c o1 n1 η + Cy1c o1 o2 n1 n2 η w := rfl
  rcases lt_or_ge (p σ) c with h0 | h0
  · have hpO := memO hp h0
    rcases lt_or_ge ((p + ev ν) σ) c with h1 | h1
    · have hpνO := memO hpν h1
      have e : gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) p ν = gt W Go p ν :=
        gt_congr (gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hpO)
          (gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hpνO)
      rw [e]; have := hO1 p ν hpO hpνO; linarith
    · have hpνN := memN hpν h1
      have hνσ : ν = σ := by
        by_contra hn; simp [ev_apply_ne (Ne.symm hn)] at h1; omega
      rw [hνσ] at hpνN h1 ⊢
      rw [gst_cross hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hpO hpνN]
      have hpl : (p + ev σ) σ = c := by simp [ev_apply_self] at h1 ⊢; omega
      have := az_bound hc0 hch hO1 hpνN hpl
      linarith
  · have hpN := memN hp h0
    have hpνN : p + ev ν ∈ SlabS σ lo hi c ch := memN hpν (by
      by_cases hn : ν = σ
      · rw [hn]; simp [ev_apply_self]; omega
      · simp [ev_apply_ne (Ne.symm hn)]; omega)
    rw [gst_bond_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hpN hpνN]
    refine (gauge_step_one _ _ _).trans ?_
    have g := g0_c1 hc0 hch hO1 hN1 hH ho1 hn1 hη (Gn := Gn) p ν hpN hpνN
    have cd := frobNorm_cay_sub_le (fz_su2 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh (τ₁ := τ₁) (τ₂ := τ₂)
      (w := w) (p + ev ν)) (fz_su2 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh (τ₁ := τ₁) (τ₂ := τ₂) (w := w) p)
    have fd := fz_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hpN hpνN
    have : Cy1c o1 o2 n1 n2 η w = (9 / 2) * F1c o1 o2 n1 n2 η w := rfl
    nlinarith

theorem stack2_c2_N {p : Z3} {μ ν : Fin 3} (h0 : p ∈ SlabS σ lo hi c ch) (h1 : p + ev ν ∈ SlabS σ lo hi c ch)
    (h2 : p + ev μ ∈ SlabS σ lo hi c ch) (h3 : p + ev μ + ev ν ∈ SlabS σ lo hi c ch) :
    frobNorm (((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) (p + ev μ) ν : SU2) : M2)
      - ((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) p ν : SU2) : M2))
      ≤ g02c o1 o2 n1 n2 η + g01c o1 n1 η * (2 * Cy1c o1 o2 n1 n2 η w)
        + Cy1c o1 o2 n1 n2 η w * Cy1c o1 o2 n1 n2 η w + Cy2c o1 o2 n1 n2 η w := by
  obtain ⟨hk, hg1, hg2, hv, hd, hf1, hf2, hc1, hc2⟩ := nonnegs hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw
  rw [gst_bond_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw h0 h1,
    gst_bond_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw h2 h3]
  set F := Fz W σ τ₁ τ₂ c lo hi Go Gn w
  have su : ∀ q, IsSu2 (F q) := fun q => fz_su2 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh q
  refine (gauge_step_two (cay (F p)) (cay (F (p + ev ν))) (cay (F (p + ev μ))) (cay (F (p + ev μ + ev ν)))
    (gt W (G0 W σ c Go Gn) p ν) (gt W (G0 W σ c Go Gn) (p + ev μ) ν)).trans ?_
  have dF : ∀ q ρ, q ∈ SlabS σ lo hi c ch → q + ev ρ ∈ SlabS σ lo hi c ch →
      frobNorm (((cay (F (q + ev ρ)) : SU2) : M2) - (cay (F q) : M2)) ≤ Cy1c o1 o2 n1 n2 η w := by
    intro q ρ hq hqρ
    have a := frobNorm_cay_sub_le (su (q + ev ρ)) (su q)
    have b := fz_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hq hqρ (w := w)
    unfold Cy1c; nlinarith
  have k20 := dF p μ h0 h2
  have k31 : frobNorm (((cay (F (p + ev μ + ev ν)) : SU2) : M2) - (cay (F (p + ev ν)) : M2)) ≤ Cy1c o1 o2 n1 n2 η w := by
    have := dF (p + ev ν) μ h1 (by rw [show p + ev ν + ev μ = p + ev μ + ev ν by abel]; exact h3)
    rwa [show p + ev ν + ev μ = p + ev μ + ev ν by abel] at this
  have k32 := dF (p + ev μ) ν h2 h3
  have k2 : frobNorm (((cay (F (p + ev μ + ev ν)) : SU2) : M2) - (cay (F (p + ev μ)) : M2)
      - (((cay (F (p + ev ν)) : SU2) : M2) - (cay (F p) : M2))) ≤ Cy2c o1 o2 n1 n2 η w := by
    refine (cay_second4 (su p) (su (p + ev ν)) (su (p + ev μ)) (su (p + ev μ + ev ν))).trans ?_
    have d2 := fz_d2 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw h0 h1 h2 h3 (w := w)
    have e31 : frobNorm (F (p + ev μ + ev ν) - F (p + ev ν)) ≤ F1c o1 o2 n1 n2 η w := by
      have := fz_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw h1
        (by rw [show p + ev ν + ev μ = p + ev μ + ev ν by abel]; exact h3) (w := w) (ν := μ)
      rwa [show p + ev ν + ev μ = p + ev μ + ev ν by abel] at this
    have e20 := fz_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw h0 h2 (w := w)
    have e10 := fz_d1 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw h0 h1 (w := w)
    unfold Cy2c
    have : (frobNorm (F (p + ev μ + ev ν) - F (p + ev ν)) + frobNorm (F (p + ev μ) - F p)) * frobNorm (F (p + ev ν) - F p)
        ≤ (2 * F1c o1 o2 n1 n2 η w) * F1c o1 o2 n1 n2 η w :=
      mul_le_mul (by linarith) e10 (frobNorm_nonneg _) (by positivity)
    nlinarith
  have gG := g0_c2 hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 p μ ν h0 h1 h2 h3
  have gG1 := g0_c1 hc0 hch hO1 hN1 hH ho1 hn1 hη (Gn := Gn) p ν h0 h1
  have m1 : frobNorm (((gt W (G0 W σ c Go Gn) p ν : SU2) : M2) - 1)
      * (frobNorm (((cay (F (p + ev μ)) : SU2) : M2) - (cay (F p) : M2))
        + frobNorm (((cay (F (p + ev μ + ev ν)) : SU2) : M2) - (cay (F (p + ev ν)) : M2)))
      ≤ g01c o1 n1 η * (2 * Cy1c o1 o2 n1 n2 η w) := mul_le_mul gG1 (by linarith) (add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)) hg1
  have m2 : frobNorm (((cay (F (p + ev μ)) : SU2) : M2) - (cay (F p) : M2))
      * frobNorm (((cay (F (p + ev μ + ev ν)) : SU2) : M2) - (cay (F (p + ev μ)) : M2))
      ≤ Cy1c o1 o2 n1 n2 η w * Cy1c o1 o2 n1 n2 η w := mul_le_mul k20 k32 (frobNorm_nonneg _) hc1
  linarith

/-- **clause 2 of the glued gauge.** -/
theorem stack2_c2 : C2 W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) (SlabS σ lo hi c0 ch) (T2st o1 o2 n1 n2 η w) := by
  obtain ⟨hk, hg1, hg2, hv, hd, hf1, hf2, hc1, hc2⟩ := nonnegs hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw
  intro p μ ν h0 h1 h2 h3
  have hT : T2st o1 o2 n1 n2 η w = o2 + (η + o2 + 2 * o1 * o1) + (g02c o1 o2 n1 n2 η + g01c o1 n1 η * (2 * Cy1c o1 o2 n1 n2 η w)
    + Cy1c o1 o2 n1 n2 η w * Cy1c o1 o2 n1 n2 η w + Cy2c o1 o2 n1 n2 η w) := rfl
  have hNb := stack2_c2_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw (p := p) (μ := μ) (ν := ν)
  have Ob : ∀ (hO0 : p ∈ SlabS σ lo hi c0 c) (hO1' : p + ev ν ∈ SlabS σ lo hi c0 c) (hO2' : p + ev μ ∈ SlabS σ lo hi c0 c)
      (hO3 : p + ev μ + ev ν ∈ SlabS σ lo hi c0 c),
      frobNorm (((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) (p + ev μ) ν : SU2) : M2)
        - ((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) p ν : SU2) : M2)) ≤ o2 := by
    intro a b cc d
    have gO := fun q (hq : q ∈ SlabS σ lo hi c0 c) => gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw hq
    rw [gt_congr (gO _ cc) (gO _ d), gt_congr (gO _ a) (gO _ b)]
    exact hO2 p μ ν a b cc d
  have hpos : 0 ≤ η + o2 + 2 * o1 * o1 := by positivity
  have hNpos : 0 ≤ g02c o1 o2 n1 n2 η + g01c o1 n1 η * (2 * Cy1c o1 o2 n1 n2 η w)
    + Cy1c o1 o2 n1 n2 η w * Cy1c o1 o2 n1 n2 η w + Cy2c o1 o2 n1 n2 η w := by positivity
  set s := p σ with hs
  have cν : (p + ev ν) σ = s + (if ν = σ then 1 else 0) := by
    by_cases h : ν = σ
    · rw [h]; simp [ev_apply_self, hs]
    · simp [ev_apply_ne (Ne.symm h), h, hs]
  have cμ : (p + ev μ) σ = s + (if μ = σ then 1 else 0) := by
    by_cases h : μ = σ
    · rw [h]; simp [ev_apply_self, hs]
    · simp [ev_apply_ne (Ne.symm h), h, hs]
  have cμν : (p + ev μ + ev ν) σ = s + (if μ = σ then 1 else 0) + (if ν = σ then 1 else 0) := by
    rw [Pi.add_apply, cμ]
    by_cases h : ν = σ
    · rw [h]; simp [ev_apply_self]
    · simp [ev_apply_ne (Ne.symm h), h]
  -- generic: all in O or all in N
  have allO : s + 2 < c → frobNorm (((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) (p + ev μ) ν : SU2) : M2)
      - ((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) p ν : SU2) : M2)) ≤ T2st o1 o2 n1 n2 η w := by
    intro hlt
    have := Ob (memO h0 (by omega)) (memO h1 (by rw [cν]; split_ifs <;> omega)) (memO h2 (by rw [cμ]; split_ifs <;> omega))
      (memO h3 (by rw [cμν]; split_ifs <;> omega))
    linarith
  have allN : c ≤ s → frobNorm (((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) (p + ev μ) ν : SU2) : M2)
      - ((gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) p ν : SU2) : M2)) ≤ T2st o1 o2 n1 n2 η w := by
    intro hge
    have := hNb (memN h0 (by omega)) (memN h1 (by rw [cν]; split_ifs <;> omega)) (memN h2 (by rw [cμ]; split_ifs <;> omega))
      (memN h3 (by rw [cμν]; split_ifs <;> omega))
    linarith
  rcases le_or_gt c s with hge | hlt
  · exact allN hge
  by_cases hμσ : μ = σ <;> by_cases hνσ : ν = σ
  · -- μ = ν = σ
    rcases lt_or_ge (s + 2) c with hl | hl
    · exact allO hl
    have hμ' := hμσ; have hν' := hνσ
    simp only [hμσ, hνσ] at h1 h2 h3 ⊢
    rcases (show s = c - 2 ∨ s = c - 1 by omega) with e | e
    · -- (p,σ) in O, (p+σ,σ) crossing
      have pO : p ∈ SlabS σ lo hi c0 c := memO h0 (by omega)
      have p1O : p + ev σ ∈ SlabS σ lo hi c0 c := memO h1 (by simp [ev_apply_self]; omega)
      have p2N : p + ev σ + ev σ ∈ SlabS σ lo hi c ch := memN h3 (by simp [ev_apply_self]; omega)
      rw [gst_cross hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw p1O p2N]
      have g0 : gt W (Gst W σ τ₁ τ₂ c ch lo hi Go Gn w) p σ = gt W Go p σ :=
        gt_congr (gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw pO)
          (gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw p1O)
      rw [g0]
      simp only [Az, show p + ev σ + ev σ - ev σ - ev σ = p by abel, sub_self, frobNorm_zero']
      linarith
    · -- (p,σ) crossing, (p+σ,σ) inside N
      have pO : p ∈ SlabS σ lo hi c0 c := memO h0 (by omega)
      have p1N : p + ev σ ∈ SlabS σ lo hi c ch := memN h1 (by simp [ev_apply_self]; omega)
      have p2N : p + ev σ + ev σ ∈ SlabS σ lo hi c ch := memN h3 (by simp [ev_apply_self]; omega)
      have pl : (p + ev σ) σ = c := by simp [ev_apply_self]; omega
      have pl1 : (p + ev σ + ev σ) σ = c + 1 := by simp [ev_apply_self]; omega
      rw [gst_cross hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw pO p1N,
        gst_bond_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw p1N p2N,
        fz_plane hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh pl,
        fz_one hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hw p2N pl1,
        show bp σ c (p + ev σ + ev σ) = p + ev σ by rw [bp_add_self, bp_of_plane σ pl],
        cay_vf hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm p1N pl, cay_zero]
      simp only [hV]
      rw [show (1 : SU2) * gt W (G0 W σ c Go Gn) (p + ev σ) σ * ((Az W σ Go (p + ev σ))⁻¹
          * gt W (G0 W σ c Go Gn) (p + ev σ) σ)⁻¹ = Az W σ Go (p + ev σ) by group, sub_self, frobNorm_zero']
      linarith
  · -- μ = σ, ν ≠ σ
    rcases lt_or_ge (s + 1) c with hl | hl
    · have := Ob (memO h0 (by omega)) (memO h1 (by rw [cν]; split_ifs <;> omega)) (memO h2 (by rw [cμ]; split_ifs <;> omega))
        (memO h3 (by rw [cμν]; split_ifs <;> omega))
      linarith
    have e : s = c - 1 := by omega
    rw [hμσ] at h2 h3 ⊢
    have pO : p ∈ SlabS σ lo hi c0 c := memO h0 (by omega)
    have pνO : p + ev ν ∈ SlabS σ lo hi c0 c := memO h1 (by simp [ev_apply_ne (Ne.symm hνσ)]; omega)
    have p1N : p + ev σ ∈ SlabS σ lo hi c ch := memN h2 (by simp [ev_apply_self]; omega)
    have p1νN : p + ev σ + ev ν ∈ SlabS σ lo hi c ch := memN h3 (by simp [ev_apply_self, ev_apply_ne (Ne.symm hνσ)]; omega)
    have pl : (p + ev σ) σ = c := by simp [ev_apply_self]; omega
    have plν : (p + ev σ + ev ν) σ = c := by simp [ev_apply_self, ev_apply_ne (Ne.symm hνσ)]; omega
    rw [gst_bond_N hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw p1N p1νN,
      fz_plane hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh pl,
      fz_plane hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh plν, cay_zero,
      gt_congr (gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw pO)
        (gst_O hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw pνO),
      g0_plane W σ c Go Gn pl hνσ, show p + ev σ - ev σ = p by abel]
    rw [show (1 : SU2) * ((Az W σ Go (p + ev σ))⁻¹ * (Go p * (hol W p ν σ)⁻¹ * (Go p)⁻¹) * gt W Go p ν
        * Az W σ Go (p + ev σ + ev ν)) * (1 : SU2)⁻¹
        = (Az W σ Go (p + ev σ))⁻¹ * (Go p * (hol W p ν σ)⁻¹ * (Go p)⁻¹) * gt W Go p ν
          * Az W σ Go (p + ev σ + ev ν) by group]
    refine (su2_cross_bound _ _ _ _).trans ?_
    have hHb : frobNorm (((Go p * (hol W p ν σ)⁻¹ * (Go p)⁻¹ : SU2) : M2) - 1) ≤ η := by
      rw [n_conj, n_inv]
      exact hH p ν σ h0 h1 (by rw [show p + ev σ = p + ev σ from rfl]; exact h2)
        (by rw [show p + ev ν + ev σ = p + ev σ + ev ν by abel]; exact h3)
    have hAd := az_diff hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw p1N pl hνσ p1νN
    have hX := hO1 p ν pO pνO
    have hA := az_bound hc0 hch hO1 p1N pl
    have : 2 * frobNorm (((gt W Go p ν : SU2) : M2) - 1) * frobNorm (((Az W σ Go (p + ev σ) : SU2) : M2) - 1)
        ≤ 2 * o1 * o1 := by
      have n1' := frobNorm_nonneg (((gt W Go p ν : SU2) : M2) - 1)
      have n2' := frobNorm_nonneg (((Az W σ Go (p + ev σ) : SU2) : M2) - 1)
      nlinarith
    linarith
  · -- μ ≠ σ, ν = σ
    rcases lt_or_ge (s + 1) c with hl | hl
    · have := Ob (memO h0 (by omega)) (memO h1 (by rw [cν]; split_ifs <;> omega)) (memO h2 (by rw [cμ]; split_ifs <;> omega))
        (memO h3 (by rw [cμν]; split_ifs <;> omega))
      linarith
    have e : s = c - 1 := by omega
    rw [hνσ] at h1 h3 ⊢
    have pO : p ∈ SlabS σ lo hi c0 c := memO h0 (by omega)
    have pμO : p + ev μ ∈ SlabS σ lo hi c0 c := memO h2 (by simp [ev_apply_ne (Ne.symm hμσ)]; omega)
    have p1N : p + ev σ ∈ SlabS σ lo hi c ch := memN h1 (by simp [ev_apply_self]; omega)
    have pμ1N : p + ev μ + ev σ ∈ SlabS σ lo hi c ch := memN h3 (by simp [ev_apply_self, ev_apply_ne (Ne.symm hμσ)]; omega)
    have pl : (p + ev σ) σ = c := by simp [ev_apply_self]; omega
    rw [gst_cross hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw pO p1N,
      gst_cross hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw pμO pμ1N,
      show p + ev μ + ev σ = p + ev σ + ev μ by abel]
    have := az_diff hc0 hch hO1 hO2 hN1 hN2 hH ho1 hn1 hη ho2 hn2 hsm hlh hτ h1σ h2σ hw p1N pl hμσ
      (by rw [show p + ev σ + ev μ = p + ev μ + ev σ by abel]; exact pμ1N)
    linarith
  · -- both transverse: all at height s < c
    have := Ob (memO h0 (by omega)) (memO h1 (by rw [cν]; split_ifs <;> omega)) (memO h2 (by rw [cμ]; split_ifs <;> omega))
      (memO h3 (by rw [cμν]; split_ifs <;> omega))
    linarith

end main

end AdalyFormal.UnifLane.Z
