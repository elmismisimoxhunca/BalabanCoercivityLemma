import GL1
import ZT4A

/-!
# GL2 -- the holonomy obstruction: `InterfaceCharts` with a constant proportional to `α₀` is FALSE
(m2_glue, 2026-10-15)

On the wrap tower `WT` (GL1) with `Uw` (flat, holonomy `-1` around every direction-0 cycle):
* `dv_negOne` : `dv (-1) = ‖-2·I‖_F > 2`.
* `no_chart` : no `ChartOn ell Uw η a' n (pt 0) r` with `r ≥ 5 T` when `7 M ℓ a' ≤ 2`
  (the ball contains the whole direction-0 cycle of `N = 7T` bonds; each chart link has `dv < a' ℓ^{-n}`; the
  telescoped product around the cycle is `g(0)(-1)g(0)⁻¹ = -1`).
* `wt_isPatch`, `wt_noUp`, `wt_notCentred` : `(n+1, pt 0)` is an INTERFACE patch (MR4's case).
* `wt_not_interfaceCharts` : `¬ InterfaceCharts ell M (n+1) d (WT …) Uw η a'` whenever `7 M ℓ a' ≤ 2`.
* `wrap_counterexample` : in the headline's form (`Lu = 7M − 1`, fine torus `scaleUp ell (n+1) Lu`, `η = ℓ^{-(n+1)}`):
  `TorusOK`, `Admissible` (every `R`), `LambdaOK2` for `Λ = ∅`, `ClassCoupled … 12 … α₀` for EVERY `α₀ > 0`, and
  `¬ InterfaceCharts` for every `a'` with `7 M ℓ a' ≤ 2`.
* `wrap_lambda_empty` : on this tower `LambdaOK2 … Λ` forces `Λ = ∅` (`1 ≤ R`) -- the headline is trivial here.
* `no_proportional_constant` : for every `C` there is `α₀ > 0` with `ClassCoupled` and `¬ InterfaceCharts (C·12Mα₀)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.M2Glue

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq)
open AdalyFormal.Balaban.SuTwoLogExp (M2 su2NegOne coe_su2NegOne)
open AdalyFormal.M1NonFlat (SU2)
open AdalyFormal.CurvBlock (dv dv_mul dv_one chart chart_exp dv_exp_le)
open AdalyFormal.M1 (IsPatch gsp strat_eq_iff)
open AdalyFormal.M2Route (ChartOn chartRad InterfaceCharts CentredIn cz)

variable {L : PeriodicLatticeExtent}

theorem negOne_central (g : SU2) : g * su2NegOne * g⁻¹ = su2NegOne := by
  have h : g * su2NegOne = su2NegOne * g := by
    apply Subtype.ext
    show (g : M2) * ((su2NegOne : SU2) : M2) = ((su2NegOne : SU2) : M2) * (g : M2)
    rw [coe_su2NegOne]; simp
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem dv_negOne : 2 < dv (su2NegOne : SU2) := by
  unfold dv frobNorm
  rw [coe_su2NegOne]
  have h8 : frobSq ((-1 : M2) - 1) = 8 := by
    unfold frobSq
    simp [Matrix.sub_apply, Matrix.one_apply, Complex.normSq]
    norm_num
  rw [h8, Real.lt_sqrt (by norm_num)]; norm_num

section wrap
variable {M ell n : ℕ} (hM : 0 < M) (hell : 0 < ell) (hn : 1 ≤ n)
  (hL : ∀ μ, L μ + 1 = 7 * (M * ell ^ (n + 1)))
include hM hell hn hL

theorem N_pos : 0 < 7 * (M * ell ^ (n + 1)) := by positivity

/-- the point `t` steps along direction 0 from the origin. -/
def pt (t : ℕ) : PeriodicLatticeSite L :=
  mkN hL (fun σ => if σ = 0 then t % (7 * (M * ell ^ (n + 1))) else 0)
    (fun σ => by have := N_pos hM hell hn hL; split_ifs <;> [exact Nat.mod_lt _ this; exact this])

theorem pt_val (t : ℕ) (σ : Fin 3) :
    ((pt hM hell hn hL t) σ).val = if σ = 0 then t % (7 * (M * ell ^ (n + 1))) else 0 := rfl

theorem pt_shift (t : ℕ) : periodicLatticeShift (pt hM hell hn hL t) 0 = pt hM hell hn hL (t + 1) := by
  funext σ
  apply Fin.ext
  rw [shift_val']
  simp only [pt_val]
  have hN := N_pos hM hell hn hL
  have hl := hL 0
  have h2 : 2 ≤ 7 * (M * ell ^ (n + 1)) := by
    have : 1 ≤ M * ell ^ (n + 1) := Nat.mul_pos hM (pow_pos hell _); omega
  have hm := Nat.mod_lt t hN
  have key : (if t % (7 * (M * ell ^ (n + 1))) = L 0 then 0 else t % (7 * (M * ell ^ (n + 1))) + 1)
      = (t + 1) % (7 * (M * ell ^ (n + 1))) := by
    rw [Nat.add_mod t 1, Nat.mod_eq_of_lt (show 1 < 7 * (M * ell ^ (n + 1)) by omega)]
    split_ifs with h
    · rw [h, show L 0 + 1 = 7 * (M * ell ^ (n + 1)) from hl, Nat.mod_self]
    · exact (Nat.mod_eq_of_lt (by omega)).symm
  by_cases hσ : σ = 0
  · subst hσ
    simpa using key
  · simp only [if_neg hσ]

theorem pt_N : pt hM hell hn hL (7 * (M * ell ^ (n + 1))) = pt hM hell hn hL 0 := by
  funext σ; apply Fin.ext; rw [pt_val, pt_val, Nat.mod_self, Nat.zero_mod]

theorem pdist_pt (t : ℕ) : pdist (pt hM hell hn hL 0) (pt hM hell hn hL t) ≤ 5 * (M * ell ^ (n + 1)) := by
  unfold pdist
  rw [Fin.sum_univ_three]
  simp only [pt_val, if_pos rfl, Nat.zero_mod, if_neg (show (1 : Fin 3) ≠ 0 by decide),
    if_neg (show (2 : Fin 3) ≠ 0 by decide)]
  unfold pcd
  have hN := N_pos hM hell hn hL
  have hm := Nat.mod_lt t hN
  have hl1 := hL 1
  have hl2 := hL 2
  have hl0 := hL 0
  simp only [le_refl, if_true, Nat.sub_zero, Nat.sub_self, min_self, zero_le, min_eq_left]
  rw [hl0]
  rcases le_total (t % (7 * (M * ell ^ (n + 1)))) (5 * (M * ell ^ (n + 1))) with h | h
  · have := min_le_left (t % (7 * (M * ell ^ (n + 1)))) (7 * (M * ell ^ (n + 1)) - t % (7 * (M * ell ^ (n + 1))))
    omega
  · have := min_le_right (t % (7 * (M * ell ^ (n + 1)))) (7 * (M * ell ^ (n + 1)) - t % (7 * (M * ell ^ (n + 1))))
    omega

/-- a chart link has `dv < a' ℓ^{-n}`. -/
theorem chart_link_dv {η a' : ℝ} (hη : 0 < η) {g : PeriodicLatticeSite L → SU2} {A : Bond L → M2}
    (hHT : ∀ e, AdalyFormal.StatementLane.HT (A e)) (e : Bond L)
    (hUA : ((periodicGaugeTransform g Uw e : SU2) : M2) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (h1 : frobNorm (A e) < a' * (((ell : ℝ) ^ n * η)⁻¹ ^ 1)) :
    dv (periodicGaugeTransform g Uw e) < a' * ((ell : ℝ) ^ n)⁻¹ := by
  obtain ⟨hX, hXn⟩ := chart η hη.le (A e) ⟨(hHT e).1, (hHT e).2⟩
  rw [chart_exp _ hX _ hUA]
  refine lt_of_le_of_lt (dv_exp_le hX) ?_
  rw [hXn]
  have hp : (0 : ℝ) < (ell : ℝ) ^ n := by
    have : (0 : ℝ) < ell := (by exact_mod_cast hell)
    positivity
  have : η * (a' * (((ell : ℝ) ^ n * η)⁻¹ ^ 1)) = a' * ((ell : ℝ) ^ n)⁻¹ := by
    field_simp
  rw [← this]
  exact mul_lt_mul_of_pos_left h1 hη

/-- **the holonomy obstruction**. -/
theorem no_chart {η a' : ℝ} (hη : 0 < η) (ha : 7 * (M : ℝ) * ell * a' ≤ 2) {r : ℕ}
    (hr : 5 * (M * ell ^ (n + 1)) ≤ r) : ¬ ChartOn ell Uw η a' n (pt hM hell hn hL 0) r := by
  rintro ⟨g, A, hHT, hUA, h1, -⟩
  set N := 7 * (M * ell ^ (n + 1)) with hNdef
  set δ : ℝ := a' * ((ell : ℝ) ^ n)⁻¹ with hδ
  have hN := N_pos hM hell hn hL
  have hlink : ∀ t, dv (periodicGaugeTransform g Uw (pt hM hell hn hL t, 0)) < δ := fun t =>
    chart_link_dv hM hell hn hL hη hHT _ (hUA _ ((pdist_pt hM hell hn hL t).trans hr))
      (h1 _ ((pdist_pt hM hell hn hL t).trans hr))
  have hδ0 : 0 ≤ δ := le_of_lt (lt_of_le_of_lt (AdalyFormal.CurvBlock.dv_nonneg _) (hlink 0))
  have hU1 : ∀ t, t + 1 < N → Uw (pt hM hell hn hL t, 0) = 1 := by
    intro t ht
    unfold Uw
    rw [if_neg]
    rintro ⟨-, h2⟩
    rw [pt_val, if_pos rfl, Nat.mod_eq_of_lt (by omega)] at h2
    have := hL 0; omega
  have hind : ∀ t, t + 1 ≤ N → dv (g (pt hM hell hn hL 0) * (g (pt hM hell hn hL t))⁻¹) ≤ t * δ := by
    intro t
    induction t with
    | zero => intro _; rw [mul_inv_cancel, dv_one]; simp
    | succ t ih =>
      intro ht
      have hstep : g (pt hM hell hn hL 0) * (g (pt hM hell hn hL (t + 1)))⁻¹ =
          (g (pt hM hell hn hL 0) * (g (pt hM hell hn hL t))⁻¹) *
            periodicGaugeTransform g Uw (pt hM hell hn hL t, 0) := by
        unfold periodicGaugeTransform
        simp only
        rw [hU1 t (by omega), pt_shift]
        group
      rw [hstep]
      refine (dv_mul _ _).trans ?_
      have := ih (by omega)
      have := (hlink t).le
      push_cast; linarith
  have hlast : Uw (pt hM hell hn hL (N - 1), 0) = su2NegOne := by
    unfold Uw
    rw [if_pos]
    refine ⟨rfl, ?_⟩
    rw [pt_val, if_pos rfl, Nat.mod_eq_of_lt (by omega)]
    have := hL 0; omega
  have hfin : (g (pt hM hell hn hL 0) * (g (pt hM hell hn hL (N - 1)))⁻¹) *
      periodicGaugeTransform g Uw (pt hM hell hn hL (N - 1), 0) = su2NegOne := by
    unfold periodicGaugeTransform
    simp only
    rw [hlast, pt_shift, show N - 1 + 1 = N by omega, pt_N]
    rw [show g (pt hM hell hn hL 0) * (g (pt hM hell hn hL (N - 1)))⁻¹ *
        (g (pt hM hell hn hL (N - 1)) * su2NegOne * (g (pt hM hell hn hL 0))⁻¹)
        = g (pt hM hell hn hL 0) * su2NegOne * (g (pt hM hell hn hL 0))⁻¹ by group]
    exact negOne_central _
  have hb := (dv_mul _ _).trans_lt
    (add_lt_add_of_le_of_lt (hind (N - 1) (by omega)) (hlink (N - 1)))
  rw [hfin] at hb
  have hneg := dv_negOne
  have hcast : (((N - 1 : ℕ) : ℝ) * δ + δ) = (N : ℝ) * δ := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hb
  have hNd : (N : ℝ) * δ = 7 * (M : ℝ) * ell * a' := by
    rw [hδ, hNdef]
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    push_cast
    field_simp
    ring
  rw [hNd] at hb
  linarith

theorem wt_isPatch (R : ℕ) : IsPatch ell M (n + 1) 1 (WT L M ell n) (n + 1) (pt hM hell hn hL 0) := by
  refine ⟨le_rfl, fun σ => ?_, pt hM hell hn hL 0, by rw [wt_le (Nat.zero_le n)]; trivial, ?_, fun _ => rfl⟩
  · rw [pt_val]; split_ifs <;> simp
  · have hmem : pt hM hell hn hL 0 ∈ towerBj (WT L M ell n) (n + 1) := by
      refine ⟨?_, ?_⟩
      · rw [wt_top]; intro σ; rw [pt_val]
        have := Nat.mul_pos hM (pow_pos hell (n + 1))
        split_ifs
        · rw [Nat.zero_mod]; exact this
        · exact this
      · rw [wt_gt (by omega)]; exact fun h => h
    exact ((strat_eq_iff (wt_admissible hM hell hn hL R) le_rfl _).mp hmem).2

theorem wt_noUp (w : PeriodicLatticeSite L) (rad : ℕ) :
    ¬ ∃ y ∈ Ball w rad, y ∈ (WT L M ell n).Om (n + 1 + 1) := by
  rintro ⟨y, -, hy⟩; rw [wt_gt (by omega)] at hy; exact hy

theorem wt_notCentred (w : PeriodicLatticeSite L) : ¬ CentredIn (WT L M ell n) ell M (n + 1) w := by
  intro h
  have hin : pT hM hell hL ∈ siteBox (cz (bigSide M ell (n + 1)) w) (12 * bigSide M ell (n + 1)) := by
    intro σ
    have hl := hL σ
    have hT : 0 < M * ell ^ (n + 1) := Nat.mul_pos hM (pow_pos hell _)
    refine lt_of_lt_of_le (Nat.mod_lt _ (by omega)) ?_
    unfold bigSide; omega
  have := h hin
  rw [wt_top] at this
  exact pT_not_blk hM hell hn hL this

/-- **`InterfaceCharts` fails on the wrap tower for every `a'` with `7 M ℓ a' ≤ 2`.** -/
theorem wt_not_interfaceCharts (d : ℕ) {η a' : ℝ} (hη : 0 < η) (ha : 7 * (M : ℝ) * ell * a' ≤ 2) :
    ¬ InterfaceCharts ell M (n + 1) d (WT L M ell n) Uw η a' := by
  intro h
  have hc := h (n + 1) (pt hM hell hn hL 0) (wt_isPatch hM hell hn hL 0) (by omega)
    (wt_noUp hM hell hn hL _ _) (wt_notCentred hM hell hn hL _)
  rw [Nat.add_sub_cancel] at hc
  refine no_chart hM hell hn hL hη ha ?_ hc
  unfold chartRad gsp bigSide
  simp only [one_mul]
  omega

end wrap

/-! ## the headline form -/

/-- the unit torus `7M` per side. -/
def Lu7 (M : ℕ) : PeriodicLatticeExtent := fun _ => 7 * M - 1

theorem hL7 {M ell n : ℕ} (hM : 0 < M) (hell : 0 < ell) :
    ∀ μ, scaleUp ell (n + 1) (Lu7 M) μ + 1 = 7 * (M * ell ^ (n + 1)) := by
  intro μ
  unfold scaleUp Lu7
  have h1 : 7 * M - 1 + 1 = 7 * M := by omega
  rw [h1]
  have : 0 < 7 * M * ell ^ (n + 1) := by positivity
  rw [Nat.sub_add_cancel (by omega)]; ring

theorem torusOK7 {M ell : ℕ} (hM : 0 < M) (hell : 0 < ell) (hdvd : ell ∣ M) : TorusOK ell M (Lu7 M) := by
  have h1 : ∀ μ, Lu7 M μ + 1 = 7 * M := fun μ => by unfold Lu7; omega
  have hle := Nat.le_of_dvd hM hdvd
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩
  · rw [h1]; exact Dvd.dvd.mul_left hdvd 7
  · rw [h1]; omega
  · rw [h1]; exact Dvd.intro_left 7 rfl

theorem lambdaOK2_empty {M ell n R : ℕ} (hM : 0 < M) (hell : 0 < ell) :
    LambdaOK2 ell M R (n + 1) (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n)
      (∅ : Set (PeriodicLatticeSite (Lu7 M))) := by
  have hL := hL7 (n := n) hM hell
  refine ⟨⟨fun x hx => hx.elim, ?_⟩, fun x hx => hx.elim⟩
  refine ⟨fun y μ => ⟨ell ^ (n + 1) * (y μ).val, ?_⟩, fun y μ => rfl, fun y hy => hy.elim, fun y hy => hy.elim⟩
  have hy := (y μ).isLt
  have h1 : Lu7 M μ + 1 = 7 * M := by unfold Lu7; omega
  have hy' : (y μ).val < 7 * M := by omega
  rw [hL μ]
  have hp : 0 < ell ^ (n + 1) := pow_pos hell _
  calc ell ^ (n + 1) * (y μ).val < ell ^ (n + 1) * (7 * M) := Nat.mul_lt_mul_of_pos_left hy' hp
    _ = 7 * (M * ell ^ (n + 1)) := by ring

/-- on the wrap tower `LambdaOK2` forces `Λ = ∅` (the top stratum is one block, no `RM` collar fits). -/
theorem wrap_lambda_empty {M ell n R : ℕ} (hM : 0 < M) (hell : 0 < ell) (hR : 1 ≤ R)
    (Λ : Set (PeriodicLatticeSite (Lu7 M)))
    (h : LambdaOK2 ell M R (n + 1) (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n) Λ) : Λ = ∅ := by
  obtain ⟨⟨-, emb, hv, hin, hout⟩, -⟩ := h
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have h1 : ∀ μ, Lu7 M μ + 1 = 7 * M := fun μ => by unfold Lu7; omega
  have hp : 0 < ell ^ (n + 1) := pow_pos hell _
  have hyb : ∀ σ, (y σ).val < M := by
    intro σ
    have := hin y hy
    rw [wt_top] at this
    have h2 := this σ
    rw [hv] at h2
    by_contra hc; push_neg at hc
    have : ell ^ (n + 1) * M ≤ ell ^ (n + 1) * (y σ).val := Nat.mul_le_mul_left _ hc
    rw [mul_comm M] at h2; omega
  let y' : PeriodicLatticeSite (Lu7 M) := fun σ =>
    if hσ : σ = 0 then ⟨M, by have := h1 σ; omega⟩ else y σ
  have hy'out : emb y' ∉ (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n).Om (n + 1) := by
    rw [wt_top]; intro h2
    have h3 := h2 0
    rw [hv] at h3
    simp only [y', dif_pos rfl] at h3
    rw [mul_comm] at h3; omega
  have hd := hout y hy y' hy'out
  have hle : pdist y y' ≤ M := by
    unfold pdist
    rw [Fin.sum_univ_three]
    simp only [y', dif_pos rfl, dif_neg (show (1 : Fin 3) ≠ 0 by decide), dif_neg (show (2 : Fin 3) ≠ 0 by decide)]
    unfold pcd
    have := hyb 0
    simp only [le_refl, if_true, Nat.sub_self, zero_le, min_eq_left, add_zero]
    rw [if_pos (by omega)]
    exact (min_le_left _ _).trans (by omega)
  have : R * M ≥ M := Nat.le_mul_of_pos_left M hR
  omega

/-- **the counterexample, headline form.** -/
theorem wrap_counterexample {ell M n R : ℕ} (hell2 : 2 ≤ ell) (hell11 : ell ≤ 11) (hM : 0 < M) (hdvd : ell ∣ M)
    (hn : 1 ≤ n) (hR : 3 * 12 ≤ R * ell) (d : ℕ) :
    TorusOK ell M (Lu7 M) ∧
    Admissible ell M R (n + 1) (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n) ∧
    LambdaOK2 ell M R (n + 1) (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n) (∅ : Set (PeriodicLatticeSite (Lu7 M))) ∧
    (∀ α₀ : ℝ, 0 < α₀ →
      ClassCoupled ell M 12 (n + 1) (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n) α₀ (((ell : ℝ) ^ (n + 1))⁻¹) Uw) ∧
    (∀ η a' : ℝ, 0 < η → 7 * (M : ℝ) * ell * a' ≤ 2 →
      ¬ InterfaceCharts ell M (n + 1) d (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n) Uw η a') := by
  have hell : 0 < ell := by omega
  have hL := hL7 (n := n) hM hell
  refine ⟨torusOK7 hM hell hdvd, wt_admissible hM hell hn hL R, lambdaOK2_empty hM hell, fun α₀ hα => ?_,
    fun η a' hη ha => wt_not_interfaceCharts hM hell hn hL d hη ha⟩
  have : (0 : ℝ) < ((ell : ℝ) ^ (n + 1))⁻¹ := by
    have : (0 : ℝ) < ell := (by exact_mod_cast hell)
    positivity
  exact wt_classCoupled hM hell hn hL hell2 hell11 hR α₀ _ hα this

/-- **no constant `C` (independent of `α₀`) makes `InterfaceCharts (C · 12 M α₀)` follow from the class.** -/
theorem no_proportional_constant {ell M n R : ℕ} (hell2 : 2 ≤ ell) (hell11 : ell ≤ 11) (hM : 0 < M) (hdvd : ell ∣ M)
    (hn : 1 ≤ n) (hR : 3 * 12 ≤ R * ell) (d : ℕ) (C : ℝ) :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ClassCoupled ell M 12 (n + 1) (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n) α₀ (((ell : ℝ) ^ (n + 1))⁻¹) Uw ∧
      ¬ InterfaceCharts ell M (n + 1) d (WT (scaleUp ell (n + 1) (Lu7 M)) M ell n) Uw (((ell : ℝ) ^ (n + 1))⁻¹)
          (C * (12 * M * α₀)) := by
  obtain ⟨-, -, -, hcc, hno⟩ := wrap_counterexample hell2 hell11 hM hdvd hn hR d
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlr : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hC : 0 < |C| + 1 := by positivity
  refine ⟨1 / (84 * M * M * ell * (|C| + 1)), by positivity, hcc _ (by positivity), hno _ _ (by positivity) ?_⟩
  have : 7 * (M : ℝ) * ell * (C * (12 * M * (1 / (84 * M * M * ell * (|C| + 1))))) = C / (|C| + 1) := by
    field_simp; ring
  rw [this, div_le_iff₀ hC]
  have := le_abs_self C
  linarith

end AdalyFormal.M2Glue
