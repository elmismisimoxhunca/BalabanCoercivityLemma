import M2B7
import OG1
import ZR8Geo

/-!
# AU_CUT -- clause-3-free M1 regime and the region cutoff (lane allc_20261016, uniform-in-c route)

* `M1BoundsU` / `M1RegularU` : `M1Bounds` / `M1Regular` (M1B) with the third clause (`ddA`) replaced by `True` (clauses 0,1,2 kept verbatim, so that `hB.1`, `hB.2.1`, `hB.2.2.1` keep their meaning).
  No consumer in the cone reads clause 3; it was only produced by `M2B6e.cut_c3`.
* `CutSpec1` : the cutoff properties used by clauses 0-2 only (0 <= chi <= 1, 1/W-Lipschitz forward step, support).
* `rcut w T W` : radial cutoff `clamp01((T - pdist w x)/W)`.
* `cut_c1U`, `cut_htU`, `cut_c2U` : text copies of `M2B6d.cut_c1/cut_ht/cut_c2` with the class cube `hq` replaced by `k <= i + 1` (every bond has `bstrat <= k`) and `CubeData` by `OneGap.CubeData12`.
* `regime_of_region` : a `RegionChart` on `Ball w rho` at scale `ell^i` (`k <= i+1`) gives a global `V` with `M1RegularU` at `ell^3 (2 alpha0)` agreeing with `U^g` on `Ball w r`, `r + W + 5 <= rho`, `64 ell^i <= W`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.AllU

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle Ball AgreeAt)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.M1 (bstrat StratReads)
open AdalyFormal.M2Bridge

variable {L : PeriodicLatticeExtent}

/-- `M1Bounds` without clause 3 (`ddA`). -/
def M1BoundsU (S : Tower L) (ell M f k : ℕ) (α₀ η : ℝ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ e : Bond L, HT (A e)) ∧
  (∀ (e : Bond L) (j : ℕ), j ≤ bstrat S k e →
      frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
  (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      j ≤ bstrat S k (x, ν) → j ≤ bstrat S k (periodicLatticeShift x μ, ν) →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
        < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
  True

/-- `M1Regular` without clause 3. -/
def M1RegularU (ell M f k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
    M1BoundsU S ell M f k α₀ η A

/-- the (clause 3 free) regime is monotone in `α₀`. -/
theorem M1BoundsU.mono {S : Tower L} {ell M f k : ℕ} {α₀ β η : ℝ} {A : Bond L → Matrix (Fin 2) (Fin 2) ℂ}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : M1BoundsU S ell M f k α₀ η A) : M1BoundsU S ell M f k β η A := by
  have key : ∀ (j p : ℕ), (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p) ≤ (f : ℝ) * M * β * (((ell : ℝ) ^ j * η)⁻¹ ^ p) := by
    intro j p
    have hcM : (0 : ℝ) ≤ (f : ℝ) * M := by positivity
    have hX : (0 : ℝ) ≤ ((ell : ℝ) ^ j * η)⁻¹ ^ p := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ hcM) hX
  exact ⟨h.1, fun e j hj => lt_of_lt_of_le (h.2.1 e j hj) (key j 1),
    fun μ ν x j h1 h2 => lt_of_lt_of_le (h.2.2.1 μ ν x j h1 h2) (key j 2), trivial⟩

theorem M1RegularU.mono {S : Tower L} {ell M f k : ℕ} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : M1RegularU ell M f k S α₀ η U) : M1RegularU ell M f k S β η U := by
  obtain ⟨g, A, hg, hB⟩ := h
  exact ⟨g, A, hg, hB.mono hη hαβ⟩

/-! ### the cutoff -/

structure CutSpec1 (sites : Set (PeriodicLatticeSite L)) (χ : PeriodicLatticeSite L → ℝ) (τ1 : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ χ x
  le_one : ∀ x, χ x ≤ 1
  fwd : ∀ x μ, |χ (periodicLatticeShift x μ) - χ x| ≤ τ1
  supp : ∀ x, χ x ≠ 0 → ∀ y, pdist x y ≤ 6 → y ∈ sites

/-- the radial cutoff about `w`: `1` on `pdist w x <= T - W`, `0` on `pdist w x >= T`. -/
noncomputable def rcut (w : PeriodicLatticeSite L) (T W : ℕ) (x : PeriodicLatticeSite L) : ℝ :=
  max 0 (min 1 (((T : ℝ) - (pdist w x : ℝ)) / W))

theorem rcut_nonneg (w : PeriodicLatticeSite L) (T W : ℕ) (x : PeriodicLatticeSite L) : 0 ≤ rcut w T W x := le_max_left _ _

theorem rcut_le_one (w : PeriodicLatticeSite L) (T W : ℕ) (x : PeriodicLatticeSite L) : rcut w T W x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem clamp_lip (a b : ℝ) : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by
  have h1 : |min 1 a - min 1 b| ≤ |a - b| := by
    have := abs_min_sub_min_le_max 1 a 1 b
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at this
    exact this
  have h2 : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |min 1 a - min 1 b| := by
    have := abs_max_sub_max_le_abs (min 1 a) (min 1 b) 0
    rwa [max_comm (min 1 a) 0, max_comm (min 1 b) 0] at this
  exact h2.trans h1

theorem pdist_step (w x : PeriodicLatticeSite L) (μ : Fin 3) :
    |(pdist w (periodicLatticeShift x μ) : ℝ) - (pdist w x : ℝ)| ≤ 1 := by
  have h1 := pdist_triangle w x (periodicLatticeShift x μ)
  have h2 := pdist_shift_le x μ
  have h3 := pdist_triangle w (periodicLatticeShift x μ) x
  have h4 : pdist (periodicLatticeShift x μ) x ≤ 1 := by rw [pdist_comm]; exact h2
  rw [abs_le]
  constructor
  · have : pdist w x ≤ pdist w (periodicLatticeShift x μ) + 1 := le_trans h3 (by omega)
    have : (pdist w x : ℝ) ≤ (pdist w (periodicLatticeShift x μ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  · have : pdist w (periodicLatticeShift x μ) ≤ pdist w x + 1 := le_trans h1 (by omega)
    have : (pdist w (periodicLatticeShift x μ) : ℝ) ≤ (pdist w x : ℝ) + 1 := by exact_mod_cast this
    linarith

theorem rcut_fwd (w : PeriodicLatticeSite L) {T W : ℕ} (hW : 1 ≤ W) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |rcut w T W (periodicLatticeShift x μ) - rcut w T W x| ≤ 1 / (W : ℝ) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold rcut
  refine (clamp_lip _ _).trans ?_
  have : ((T : ℝ) - (pdist w (periodicLatticeShift x μ) : ℝ)) / W - ((T : ℝ) - (pdist w x : ℝ)) / W
      = -((pdist w (periodicLatticeShift x μ) : ℝ) - (pdist w x : ℝ)) / W := by field_simp; ring
  rw [this, abs_div, abs_neg, abs_of_pos hW0]
  exact div_le_div_of_nonneg_right (pdist_step w x μ) hW0.le

theorem rcut_one (w : PeriodicLatticeSite L) {T W : ℕ} (hW : 1 ≤ W) {x : PeriodicLatticeSite L}
    (hx : pdist w x + W ≤ T) : rcut w T W x = 1 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  unfold rcut
  have h : (1 : ℝ) ≤ ((T : ℝ) - (pdist w x : ℝ)) / W := by
    rw [le_div_iff₀ hW0]
    have : ((pdist w x + W : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hx
    push_cast at this; linarith
  rw [min_eq_left h]; simp

theorem rcut_supp (w : PeriodicLatticeSite L) {T W ρ : ℕ} (hW : 1 ≤ W) (hT : T + 5 ≤ ρ)
    (x : PeriodicLatticeSite L) (hx : rcut w T W x ≠ 0) : ∀ y, pdist x y ≤ 6 → y ∈ Ball w ρ := by
  intro y hy
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  by_contra hno
  have hlt : ρ < pdist w y := by
    have : ¬ pdist w y ≤ ρ := hno
    omega
  have h1 := pdist_triangle w x y
  have hxT : T ≤ pdist w x := by omega
  apply hx
  unfold rcut
  have : ((T : ℝ) - (pdist w x : ℝ)) / W ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hW0.le
    have : (T : ℝ) ≤ (pdist w x : ℝ) := by exact_mod_cast hxT
    linarith
  have h2 : min 1 (((T : ℝ) - (pdist w x : ℝ)) / W) ≤ 0 := le_trans (min_le_right _ _) this
  exact max_eq_left h2

theorem rcut_spec (w : PeriodicLatticeSite L) {T W ρ : ℕ} (hW : 1 ≤ W) (hT : T + 5 ≤ ρ) :
    CutSpec1 (Ball w ρ) (rcut w T W) (1 / (W : ℝ)) where
  nonneg := rcut_nonneg w T W
  le_one := rcut_le_one w T W
  fwd := fun x μ => rcut_fwd w hW x μ
  supp := fun x hx y hy => rcut_supp w hW hT x hx y hy

theorem cubeBond_of_chiU {sites : Set (PeriodicLatticeSite L)} {χ : PeriodicLatticeSite L → ℝ} {τ1 : ℝ}
    (hc : CutSpec1 sites χ τ1) {e : Bond L} (h : χ e.1 ≠ 0) : CubeBond sites e := by
  have hx := hc.supp e.1 h
  refine ⟨hx e.1 (by rw [pdist_self']; norm_num), hx _ ?_⟩
  have := pdist_shift_le e.1 e.2
  omega

theorem cut_hx4U {sites : Set (PeriodicLatticeSite L)} {χ : PeriodicLatticeSite L → ℝ} {τ1 : ℝ}
    (hc : CutSpec1 sites χ τ1) {x p : PeriodicLatticeSite L} (hp : χ p ≠ 0) (hxp : pdist x p ≤ 2) :
    ∀ y, pdist x y ≤ 4 → y ∈ sites := by
  intro y hy
  apply hc.supp p hp y
  have := pdist_triangle p x y
  rw [pdist_comm p x] at this
  omega

section main

variable {ell M f k i : ℕ} {S : Tower L} {α₀ η : ℝ} {sites : Set (PeriodicLatticeSite L)} {A : Bond L → M2m}
  {χ : PeriodicLatticeSite L → ℝ} {τ1 : ℝ}

theorem cut_c1U (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    (hk : k ≤ i + 1) (hd : AdalyFormal.OneGap.CubeData12 ell M f α₀ η sites i A) (hc : CutSpec1 sites χ τ1) :
    ∀ (e : Bond L) (j : ℕ), j ≤ bstrat S k e →
      frobNorm (cutA χ A e) < (f : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) * (((ell : ℝ) ^ j * η)⁻¹ ^ 1) := by
  intro e j hj
  by_cases h0 : χ e.1 = 0
  · have : cutA χ A e = 0 := by unfold cutA; rw [h0, zero_smul]
    rw [this, frob_zero']
    exact cutA_pos hell hf hM hα hη j 1
  · have hb := cubeBond_of_chiU hc h0
    have hji : j ≤ i + 1 := le_trans hj (le_trans (AdalyFormal.M1.bstrat_le S k _) hk)
    apply lt_transfer hell hη hα.le hji (by norm_num)
    have h1 := hd.c1 e hb
    have h2 : frobNorm (cutA χ A e) ≤ frobNorm (A e) := by
      unfold cutA
      rw [frob_smul, abs_of_nonneg (hc.nonneg _)]
      calc χ e.1 * frobNorm (A e) ≤ 1 * frobNorm (A e) :=
            mul_le_mul_of_nonneg_right (hc.le_one _) (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _)
        _ = frobNorm (A e) := one_mul _
    have hKX : (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1) ≤ (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ 1) := by
      have h3 : (0 : ℝ) < f := by exact_mod_cast hf
      have h4 : (0 : ℝ) < M := by exact_mod_cast hM
      have h5 : (0 : ℝ) < ell := by exact_mod_cast hell
      have : 0 ≤ (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1) := by positivity
      nlinarith
    linarith

theorem cut_htU (hc : CutSpec1 sites χ τ1) (hd : AdalyFormal.OneGap.CubeData12 ell M f α₀ η sites i A) :
    ∀ e : Bond L, HT (cutA χ A e) := by
  intro e
  by_cases h0 : χ e.1 = 0
  · have : cutA χ A e = 0 := by unfold cutA; rw [h0, zero_smul]
    rw [this]
    simp [HT]
  · have hb := cubeBond_of_chiU hc h0
    have hh := hd.ht e hb
    obtain ⟨h1, h2⟩ := hh
    unfold cutA HT
    constructor
    · rw [Matrix.conjTranspose_smul, h1]; simp
    · rw [Matrix.trace_smul, h2]; simp

theorem cut_c2U (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    (hk : k ≤ i + 1) (hd : AdalyFormal.OneGap.CubeData12 ell M f α₀ η sites i A) (hc : CutSpec1 sites χ τ1)
    (h1 : 64 * τ1 * (ell : ℝ) ^ i ≤ 1) :
    ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      j ≤ bstrat S k (x, ν) → j ≤ bstrat S k (periodicLatticeShift x μ, ν) →
      frobNorm ((η⁻¹ : ℝ) • (cutA χ A (periodicLatticeShift x μ, ν) - cutA χ A (x, ν)))
        < (f : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) * (((ell : ℝ) ^ j * η)⁻¹ ^ 2) := by
  intro μ ν x j hj1 hj2
  by_cases hz : χ x = 0 ∧ χ (periodicLatticeShift x μ) = 0
  · have : (η⁻¹ : ℝ) • (cutA χ A (periodicLatticeShift x μ, ν) - cutA χ A (x, ν)) = 0 := by
      unfold cutA; dsimp only; rw [hz.1, hz.2]; simp
    rw [this, frob_zero']
    exact cutA_pos hell hf hM hα hη j 2
  · have hex : ∃ p, χ p ≠ 0 ∧ pdist x p ≤ 1 := by
      by_cases hx0 : χ x = 0
      · refine ⟨periodicLatticeShift x μ, ?_, pdist_shift_le x μ⟩
        intro h; exact hz ⟨hx0, h⟩
      · exact ⟨x, hx0, by rw [pdist_self']; norm_num⟩
    obtain ⟨p, hp, hxp⟩ := hex
    have hx4 := cut_hx4U hc hp (by omega : pdist x p ≤ 2)
    have d0 : pdist x x ≤ 3 := by rw [pdist_self']; norm_num
    have b0 : CubeBond sites ((x, ν) : Bond L) := cubeBond_of_near hx4 (e := (x, ν)) d0
    have b1 : CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) :=
      cubeBond_of_near hx4 (e := (periodicLatticeShift x μ, ν)) (le_trans (pdist_shift_le x μ) (by norm_num))
    have hji : j ≤ i + 1 := le_trans hj1 (le_trans (AdalyFormal.M1.bstrat_le S k _) hk)
    apply lt_transfer hell hη hα.le hji (by norm_num)
    set K : ℝ := (f : ℝ) * M * α₀ with hK
    set E : ℝ := (ell : ℝ) ^ i with hE
    set X : ℝ := (E * η)⁻¹ with hX
    have h3 : (0 : ℝ) < f := by exact_mod_cast hf
    have h4 : (0 : ℝ) < M := by exact_mod_cast hM
    have h5 : (0 : ℝ) < ell := by exact_mod_cast hell
    have hK0 : 0 < K := by positivity
    have hE1 : 1 ≤ E := one_le_pow₀ (by exact_mod_cast hell)
    have hX0 : 0 < X := by rw [hX]; have : 0 < E := by linarith
                           positivity
    have hηinv : η⁻¹ = E * X := by rw [hX]; field_simp
    have τ1nn : 0 ≤ τ1 := le_trans (abs_nonneg _) (hc.fwd x μ)
    have hdiff := hd.c2 μ ν x b0 b1
    have hc1 := hd.c1 (x, ν) b0
    have id : (η⁻¹ : ℝ) • (cutA χ A (periodicLatticeShift x μ, ν) - cutA χ A (x, ν))
        = χ (periodicLatticeShift x μ) • ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          + (η⁻¹ * (χ (periodicLatticeShift x μ) - χ x)) • A (x, ν) := by
      unfold cutA; dsimp only; module
    rw [id]
    refine lt_of_le_of_lt (frob_add_le _ _) ?_
    rw [frob_smul (χ (periodicLatticeShift x μ)) _, frob_smul (η⁻¹ * (χ (periodicLatticeShift x μ) - χ x)) (A (x, ν))]
    have e1 : |χ (periodicLatticeShift x μ)| * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
        ≤ K * X ^ 2 := by
      rw [abs_of_nonneg (hc.nonneg _)]
      calc χ (periodicLatticeShift x μ) * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          ≤ 1 * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) :=
            mul_le_mul_of_nonneg_right (hc.le_one _) (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _)
        _ ≤ K * X ^ 2 := by rw [one_mul]; exact hdiff.le
    have e2 : |η⁻¹ * (χ (periodicLatticeShift x μ) - χ x)| * frobNorm (A (x, ν)) ≤ K * X ^ 2 / 64 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hη)]
      have : |χ (periodicLatticeShift x μ) - χ x| ≤ τ1 := hc.fwd x μ
      have hc1' : frobNorm (A (x, ν)) ≤ K * X := by simpa [hK, hX, hE] using hc1.le
      calc η⁻¹ * |χ (periodicLatticeShift x μ) - χ x| * frobNorm (A (x, ν)) ≤ η⁻¹ * τ1 * (K * X) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left this (inv_pos.mpr hη).le) hc1'
              (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (by positivity)
        _ = K * X ^ 2 * (τ1 * E) := by rw [hηinv]; ring
        _ ≤ K * X ^ 2 / 64 := by
            have : τ1 * E ≤ 1 / 64 := by linarith
            have hh : 0 ≤ K * X ^ 2 := by positivity
            calc K * X ^ 2 * (τ1 * E) ≤ K * X ^ 2 * (1 / 64) := mul_le_mul_of_nonneg_left this hh
              _ = K * X ^ 2 / 64 := by ring
    have hKX : 0 < K * X ^ 2 := by positivity
    calc _ ≤ K * X ^ 2 + K * X ^ 2 / 64 := add_le_add e1 e2
      _ < (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ 2) := by
        have : (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ 2) = 2 * (K * X ^ 2) := by
          rw [hK, hX, hE]; ring
        rw [this]; linarith


end main

/-! ### the region regime -/

theorem regime_of_region {ell M R f k i : ℕ} {S : Tower L} {α₀ η : ℝ}
    (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η) (hk : k ≤ i + 1)
    {U : LinkCfg L} {w : PeriodicLatticeSite L} {ρ r W : ℕ}
    (hrc : AdalyFormal.OneGap.RegionChart (Ball w ρ) ell M f α₀ η i U)
    (hW1 : 1 ≤ W) (hW : 64 * ell ^ i ≤ W) (hρ : r + W + 5 ≤ ρ) :
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (V : LinkCfg L),
      M1RegularU ell M f k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
      ∀ x ∈ Ball w r, ∀ μ : Fin 3, V (x, μ) = periodicGaugeTransform g U (x, μ) := by
  obtain ⟨g, A, hgU, hd⟩ := hrc
  have hc := rcut_spec w (T := ρ - 5) (W := W) (ρ := ρ) hW1 (by omega)
  have hWR : (64 : ℝ) * (ell : ℝ) ^ i ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have h1 : 64 * (1 / (W : ℝ)) * (ell : ℝ) ^ i ≤ 1 := by
    rw [show 64 * (1 / (W : ℝ)) * (ell : ℝ) ^ i = (64 * (ell : ℝ) ^ i) / W by ring, div_le_one hW0]
    exact hWR
  have hB : M1BoundsU S ell M f k ((ell : ℝ) ^ 3 * (2 * α₀)) η (cutA (rcut w (ρ - 5) W) A) :=
    ⟨cut_htU hc hd, cut_c1U hell hf hM hα hη hk hd hc, cut_c2U hell hf hM hα hη hk hd hc h1, trivial⟩
  refine ⟨g, Vcfg η (cutA (rcut w (ρ - 5) W) A) hB.1, ⟨fun _ => 1, cutA (rcut w (ρ - 5) W) A, fun e => ?_, hB⟩, ?_⟩
  · rw [gauge_one']; rfl
  · intro x hx μ
    have hxr : pdist w x ≤ r := hx
    have hχ : rcut w (ρ - 5) W x = 1 := rcut_one w hW1 (by omega)
    have hbond : CubeBond (Ball w ρ) ((x, μ) : Bond L) := by
      refine ⟨show pdist w x ≤ ρ by omega, show pdist w (periodicLatticeShift x μ) ≤ ρ from ?_⟩
      have h2 := pdist_triangle w x (periodicLatticeShift x μ)
      have h3 := pdist_shift_le x μ
      omega
    apply Subtype.ext
    rw [Vcfg_coe]
    unfold cutA
    dsimp only
    rw [hχ, one_smul]
    exact (hgU (x, μ) hbond).symm

end AdalyFormal.AllU

#print axioms AdalyFormal.AllU.M1BoundsU.mono
#print axioms AdalyFormal.AllU.rcut_spec
#print axioms AdalyFormal.AllU.cut_c1U
#print axioms AdalyFormal.AllU.cut_htU
#print axioms AdalyFormal.AllU.cut_c2U
#print axioms AdalyFormal.AllU.regime_of_region
