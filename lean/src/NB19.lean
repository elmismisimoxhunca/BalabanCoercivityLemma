import NB18
import AB5
/-!
# NB19 -- `prop1_level` (one level of nonabelian curvature blocking, every `ell`)

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf coarseGaugeTransform)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_gauge)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice coarseLattice_mem_fits)

variable {L : PeriodicLatticeExtent}

theorem prop1_level (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration SU2 L) (P : ℝ) (hP0 : 0 ≤ P)
    (hδ : (ell : ℝ) ^ 4 * P ≤ 1 / 100000)
    (hdvd : ∀ ρ, s * ell ∣ L ρ + 1) (hN : ∀ ρ, 2 * (s * ell) < L ρ + 1)
    (hP : ∀ z ∈ CoarseLattice L s, ∀ ν μ : Fin 3, dv (pw s V z ν μ) ≤ P)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s * ell)) (ν μ : Fin 3) :
    dv (pw (s * ell) (ubarSU2 s ell V) y ν μ)
      ≤ (ell : ℝ) ^ 2 * P + 1000000 * ((ell : ℝ) ^ 4 * P ^ 2) := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hrhs : 0 ≤ (ell : ℝ) ^ 2 * P + 1000000 * ((ell : ℝ) ^ 4 * P ^ 2) := by positivity
  by_cases hνμ : ν = μ
  · subst hνμ
    have : pw (s * ell) (ubarSU2 s ell V) y ν ν = 1 := by unfold pw; group
    rw [this, dv_one]; exact hrhs
  have hds : ∀ ρ, s ∣ L ρ + 1 := fun ρ => Nat.dvd_trans (Dvd.intro ell rfl) (hdvd ρ)
  have hys : y ∈ CoarseLattice L s := cl_mono s ell hy
  have hm : s ≤ s * ell := Nat.le_mul_of_pos_right s hell
  have hP1 : P ≤ 1 := by
    have : P ≤ (ell : ℝ) ^ 4 * P := by
      have : (1 : ℝ) ≤ (ell : ℝ) ^ 4 := one_le_pow₀ hellR
      nlinarith
    linarith
  obtain ⟨hsm, hR, harith⟩ := arith_bound (ell : ℝ) P hellR hP0 hδ
  have hsm4 : 4 * (ell : ℝ) * P ≤ 1 := by
    have : (ell : ℝ) ≤ (ell : ℝ) ^ 4 := by
      calc (ell : ℝ) = (ell : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (ell : ℝ) ^ 4 := pow_le_pow_right₀ hellR (by norm_num)
    nlinarith
  set γ := cornerGauge s V y
  set W := coarseGaugeTransform s γ V
  set A : PeriodicLatticeEdge L → M2 := fun e => su2Log (W e)
  have hcov : ubarSU2 s ell W = coarseGaugeTransform (s * ell) γ (ubarSU2 s ell V) :=
    funext (fun c => ubarSU2_gauge s ell γ V c)
  have hdv : dv (pw (s * ell) (ubarSU2 s ell V) y ν μ) = dv (pw (s * ell) (ubarSU2 s ell W) y ν μ) := by
    rw [hcov, dv_pw_cgauge]
  rw [hdv]
  have hch : ∀ b : PeriodicLatticeEdge L, Box y s (2 * (s * ell) - s) b.1 →
      Chart W A (8 * ell * P) b := fun b hb =>
    chart_of_box s ell hs hell V y hys hds hN P hP hsm4 b hb
  -- the four coarse bonds
  have bond : ∀ c : PeriodicLatticeEdge L, Box y s (s * ell) c.1 → off y c.1 c.2 = 0 →
      c.1 ∈ CoarseLattice L (s * ell) → BondOK s ell W A (8 * ell * P) c := by
    intro c hc hc2 hca
    obtain ⟨h1, h2⟩ := cone_box s ell hs y c hN hm hc hc2 (coarseLattice_mem_fits hdvd hca)
    exact ⟨fun x hx b hb => hch b (h1 x hx b hb), fun b hb => hch b (h2 b hb)⟩
  have box0 : Box y s (s * ell) y := fun σ => by rw [off_self]; exact ⟨dvd_zero s, Nat.zero_le _⟩
  have boxsh : ∀ ρ, Box y s (s * ell) (coarseShift y (s * ell) ρ) := by
    intro ρ σ
    by_cases hσ : σ = ρ
    · rw [hσ, off_shift_val _ _ _ _ (by rw [off_self]; have := hN ρ; omega), off_self]
      exact ⟨⟨ell, by ring⟩, by omega⟩
    · rw [off_shift_ne _ _ _ hσ, off_self]; exact ⟨dvd_zero s, Nat.zero_le _⟩
  have offsh : ∀ ρ σ, σ ≠ ρ → off y (coarseShift y (s * ell) ρ) σ = 0 := fun ρ σ h => by
    rw [off_shift_ne _ _ _ h, off_self]
  have b1 := bond (y, ν) box0 (off_self y ν) hy
  have b2 := bond (coarseShift y (s * ell) ν, μ) (boxsh ν) (offsh ν μ (Ne.symm hνμ))
    (coarseShift_mem_coarseLattice hdvd hy ν)
  have b3 := bond (coarseShift y (s * ell) μ, ν) (boxsh μ) (offsh μ ν hνμ)
    (coarseShift_mem_coarseLattice hdvd hy μ)
  have b4 := bond (y, μ) box0 (off_self y μ) hy
  -- ladder plaquettes
  have hfit := coarseLattice_mem_fits hdvd hy
  have hq : ∀ x ∈ stepBlockOf y s ell, ∀ t ∈ ladPlaqs s μ ell x (List.replicate ell ν),
      PlaqOK s W A (8 * ell * P) P t := by
    intro x hx t ht
    obtain ⟨t1, t2, t3⟩ := ladder_box s ell y ν μ hνμ hN hfit x hx t ht
    obtain ⟨i, -, j, -, rfl⟩ := mem_ladPlaqs_rep s ν μ ell ell x t ht
    have hxa := block_aligned s ell hy hx
    have hta := ladPlaqs_aligned s hds μ ell _ x hxa _ ht
    refine ⟨hch _ t1, hch _ t2, hch _ t3, hch _ t1, ?_⟩
    show dv (pw s (coarseGaugeTransform s γ V) _ ν μ) ≤ P
    rw [dv_pw_cgauge]
    exact hP _ hta ν μ
  have hmain := prop1_chart s ell hs hell W A (8 * ell * P) P (by positivity) hP0 hP1 hsm hR y ν μ
    hdvd hy b1 b2 b3 b4 hq
  exact le_trans hmain harith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.prop1_level
