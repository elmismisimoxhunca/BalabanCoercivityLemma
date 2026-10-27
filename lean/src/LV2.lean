import LV1

/-!
# LV2 -- cubes, faces, tilings; shift-averaged face fluxes and their exact conservation

Generic torus combinatorics (no patch): `face m μ`, `cube_split` (a cube is a face times a line), `cube_decomp`
(`cube (n ℓ) = n · cube ℓ + cube n`), `block_cube` (a lattice block is `z + off (cube m)`), `tiling`
(`Σ_x H x = Σ_{z ∈ nℤ³} Σ_{u ∈ cube n} H (z + off u)`), lattice translation invariance.

Fluxes of a bond field `c` (direction `μ`):
* `flx m c w μ = m⁻² Σ_{u ∈ face m μ} c(w + off u + (m-1) e_μ, μ)` (flux through the top `μ`-face of the box `w + [0,m)³`),
* `Fl n m c z μ = n⁻³ Σ_{v ∈ cube n} flx m c (z + off v) μ` (average over the `n³` translates of the box).
`flx_cons`, `Fl_cons` : for divergence-free `c`, `Σ_μ (flx m c (w - m e_μ) μ - flx m c w μ) = 0` (exact).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.FlatCoercivity (eU)
open AdalyFormal.M1Patch (corner corner_dvd)

variable {L : PeriodicLatticeExtent}

/-! ## cubes and faces -/

/-- the `μ`-face of the cube -/
def face (m : ℕ) (μ : Fin 3) : Finset (Fin 3 → ℕ) := (cube m).filter (fun u => u μ = 0)

theorem mem_face (m : ℕ) (μ : Fin 3) (u : Fin 3 → ℕ) : u ∈ face m μ ↔ (∀ ν, u ν < m) ∧ u μ = 0 := by
  unfold face; rw [Finset.mem_filter, mem_cube]

theorem cube_split {M : Type*} [AddCommMonoid M] (m : ℕ) (μ : Fin 3) (h : (Fin 3 → ℕ) → M) :
    ∑ u ∈ cube m, h u = ∑ u ∈ face m μ, ∑ t ∈ Finset.range m, h (Function.update u μ t) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => Function.update p.1 μ p.2) (fun w => (Function.update w μ 0, w μ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, t⟩ hp
    rw [Finset.mem_product, mem_face, Finset.mem_range] at hp
    rw [mem_cube]
    intro ν
    by_cases h : ν = μ
    · subst h; simp [hp.2]
    · rw [Function.update_of_ne h]; exact hp.1.1 ν
  · intro w hw
    rw [mem_cube] at hw
    rw [Finset.mem_product, mem_face, Finset.mem_range]
    refine ⟨⟨fun ν => ?_, by simp⟩, hw μ⟩
    show Function.update w μ 0 ν < m
    by_cases h : ν = μ
    · subst h; rw [Function.update_self]; exact lt_of_le_of_lt (Nat.zero_le _) (hw ν)
    · rw [Function.update_of_ne h]; exact hw ν
  · rintro ⟨u, t⟩ hp
    simp only [Finset.mem_product, mem_face, Finset.mem_range] at hp
    obtain ⟨⟨_, hu2⟩, _⟩ := hp
    simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
    funext ν
    by_cases h : ν = μ
    · subst h; rw [Function.update_self, hu2]
    · rw [Function.update_of_ne h]
  · intro w _
    simp
  · intro _ _; rfl

theorem card_face (m : ℕ) (hm : 0 < m) (μ : Fin 3) : (face m μ).card = m ^ 2 := by
  have h := cube_split (M := ℕ) m μ (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at h
  rw [card_cube] at h
  have : m ^ 3 = m ^ 2 * m := by ring
  rw [this] at h
  exact (Nat.eq_of_mul_eq_mul_right hm h).symm

theorem cube_decomp {M : Type*} [AddCommMonoid M] (n ℓ : ℕ) (hn : 0 < n) (g : (Fin 3 → ℕ) → M) :
    ∑ U ∈ cube (n * ℓ), g U = ∑ k ∈ cube ℓ, ∑ v ∈ cube n, g (n • k + v) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p => n • p.1 + p.2) (fun U => (fun ν => U ν / n, fun ν => U ν % n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, v⟩ hp
    simp only [Finset.mem_product, mem_cube] at hp
    rw [mem_cube]
    intro ν
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hp.1 ν; have h2 := hp.2 ν
    calc n * k ν + v ν < n * k ν + n := by omega
      _ = n * (k ν + 1) := by ring
      _ ≤ n * ℓ := Nat.mul_le_mul_left n h1
  · intro U hU
    rw [mem_cube] at hU
    rw [Finset.mem_product, mem_cube, mem_cube]
    refine ⟨fun ν => ?_, fun ν => Nat.mod_lt _ hn⟩
    exact Nat.div_lt_of_lt_mul (hU ν)
  · rintro ⟨k, v⟩ hp
    simp only [Finset.mem_product, mem_cube] at hp
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.mk.injEq]
    constructor
    · funext ν
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (hp.2 ν), zero_add]
    · funext ν
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hp.2 ν)]
  · intro U _
    funext ν
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Nat.div_add_mod (U ν) n
  · intro _ _; rfl

theorem face_decomp {M : Type*} [AddCommMonoid M] (n ℓ : ℕ) (hn : 0 < n) (μ : Fin 3) (g : (Fin 3 → ℕ) → M) :
    ∑ U ∈ face (n * ℓ) μ, g U = ∑ k ∈ face ℓ μ, ∑ v ∈ face n μ, g (n • k + v) := by
  classical
  unfold face
  rw [Finset.sum_filter, cube_decomp n ℓ hn]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.sum_filter]
  by_cases hkμ : k μ = 0
  · rw [if_pos hkμ]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hkμ, mul_zero, zero_add]
  · rw [if_neg hkμ]
    refine Finset.sum_eq_zero (fun v _ => ?_)
    rw [if_neg]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    intro h
    have : n * k μ = 0 := by omega
    rcases Nat.mul_eq_zero.mp this with h' | h'
    · omega
    · exact hkμ h'

theorem off_update (u : Fin 3 → ℕ) (μ : Fin 3) (hu : u μ = 0) (t : ℕ) :
    off L (Function.update u μ t) = off L u + t • eU L μ := by
  have : Function.update u μ t = u + Pi.single μ t := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp [hu]
    · simp [Function.update_of_ne h, h]
  rw [this, off_add, off_single]

/-! ## sites: values, blocks, tiling -/

theorem add_off_val (z : PeriodicLatticeSite L) (u : Fin 3 → ℕ) (μ : Fin 3) :
    ((z + off L u) μ).val = ((z μ).val + u μ) % (L μ + 1) := by
  rw [Pi.add_apply, Fin.val_add, off_val, Nat.add_mod_mod]

theorem iota_eq_off (n : ℕ) (Y : PeriodicLatticeSite L) (i : Fin 3 → ℕ) : iota n Y i = Y + off L (n • i) := by
  funext μ
  apply Fin.ext
  rw [add_off_val, iota_val_mod]
  rfl

theorem block_cube {M : Type*} [AddCommMonoid M] (m : ℕ) (z : PeriodicLatticeSite L)
    (hfit : ∀ μ : Fin 3, (z μ).val + m ≤ L μ + 1) (g : PeriodicLatticeSite L → M) :
    ∑ x ∈ blockOf z m, g x = ∑ u ∈ cube m, g (z + off L u) := by
  symm
  refine Finset.sum_nbij' (fun u => z + off L u) (fun x => fun μ => (x μ).val - (z μ).val) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [mem_cube] at hu
    rw [mem_blockOf]
    intro μ
    have h1 := hu μ; have h2 := hfit μ
    show (z μ).val ≤ ((z + off L u) μ).val ∧ ((z + off L u) μ).val < (z μ).val + m
    rw [add_off_val, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro x hx
    rw [mem_blockOf] at hx
    rw [mem_cube]
    intro μ
    have h1 : (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + m := hx μ
    show (x μ).val - (z μ).val < m
    omega
  · intro u hu
    rw [mem_cube] at hu
    funext μ
    have h1 := hu μ; have h2 := hfit μ
    show ((z + off L u) μ).val - (z μ).val = u μ
    rw [add_off_val, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro x hx
    rw [mem_blockOf] at hx
    funext μ
    apply Fin.ext
    have h1 : (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + m := hx μ
    rw [add_off_val]
    show ((z μ).val + ((x μ).val - (z μ).val)) % (L μ + 1) = (x μ).val
    rw [Nat.add_sub_cancel' h1.1, Nat.mod_eq_of_lt (x μ).isLt]
  · intro _ _; rfl

theorem fit_of_lat {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ L μ + 1) (z : PeriodicLatticeSite L) (hz : OnLatN m z)
    (μ : Fin 3) : (z μ).val + m ≤ L μ + 1 := by
  obtain ⟨a', ha'⟩ := hz μ
  obtain ⟨b', hb'⟩ := hdvd μ
  have hlt : m * a' < m * b' := by rw [← ha', ← hb']; exact (z μ).isLt
  have hab : a' + 1 ≤ b' := Nat.lt_of_mul_lt_mul_left hlt
  have h2 := Nat.mul_le_mul_left m hab
  rw [Nat.mul_succ] at h2
  rw [ha', hb']; omega

/-- **tiling**: `Σ_x H x = Σ_{z ∈ nℤ³} Σ_{u ∈ cube n} H (z + off u)`. -/
theorem tiling {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n) (hdvd : ∀ μ : Fin 3, n ∣ L μ + 1)
    (H : PeriodicLatticeSite L → M) :
    ∑ x, H x = ∑ z : PeriodicLatticeSite L, (if OnLatN n z then ∑ u ∈ cube n, H (z + off L u) else 0) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (corner n) H]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : OnLatN n y
  · rw [if_pos hy, ← block_cube n y (fit_of_lat hdvd y hy) H]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_blockOf_iff_corner hn y x hy).symm
  · rw [if_neg hy]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact absurd (hx ▸ corner_dvd n x) hy

theorem onLat_add_iff {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ L μ + 1) (z w : PeriodicLatticeSite L) (hw : OnLatN m w) :
    OnLatN m (z + w) ↔ OnLatN m z := by
  constructor
  · intro h μ
    have h1 := h μ
    rw [Pi.add_apply, Fin.val_add] at h1
    have h2 := (Nat.dvd_mod_iff (hdvd μ)).mp h1
    exact (Nat.dvd_add_left (hw μ)).mp h2
  · intro h μ
    rw [Pi.add_apply, Fin.val_add]
    exact (Nat.dvd_mod_iff (hdvd μ)).mpr (Nat.dvd_add (h μ) (hw μ))

theorem onLat_smul_eU {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ L μ + 1) (μ : Fin 3) : OnLatN m (m • eU L μ) := by
  intro ν
  rw [Pi.smul_apply, AdalyFormal.FlatCoercivity.fin_val_nsmul]
  exact (Nat.dvd_mod_iff (hdvd ν)).mpr (Dvd.intro _ rfl)

theorem onLat_neg {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ L μ + 1) (w : PeriodicLatticeSite L) (hw : OnLatN m w) :
    OnLatN m (-w) := by
  have h0 : OnLatN m (-w + w) := by
    rw [neg_add_cancel]; intro μ; simp
  exact (onLat_add_iff hdvd (-w) w hw).mp h0

/-- lattice sums are invariant under lattice translations. -/
theorem lat_translate {M : Type*} [AddCommMonoid M] {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ L μ + 1)
    (w : PeriodicLatticeSite L) (hw : OnLatN m w) (h : PeriodicLatticeSite L → M) :
    ∑ z : PeriodicLatticeSite L, (if OnLatN m z then h (z + w) else 0)
      = ∑ z : PeriodicLatticeSite L, (if OnLatN m z then h z else 0) := by
  classical
  rw [← sum_translate (fun z => if OnLatN m z then h z else 0) w]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  simp only [onLat_add_iff hdvd z w hw]

/-! ## Jensen for averages -/

theorem avg_sq_le {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset ι) (K : ℝ)
    (hK : (s.card : ℝ) = K) (hKp : 0 < K) (w : ι → E) :
    ‖K⁻¹ • ∑ i ∈ s, w i‖ ^ 2 ≤ K⁻¹ * ∑ i ∈ s, ‖w i‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKp)]
  have h := norm_sum_sq_le s w
  rw [hK] at h
  have hK2 : K⁻¹ ^ 2 * K = K⁻¹ := by field_simp
  calc K⁻¹ ^ 2 * ‖∑ i ∈ s, w i‖ ^ 2 ≤ K⁻¹ ^ 2 * (K * ∑ i ∈ s, ‖w i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = K⁻¹ * ∑ i ∈ s, ‖w i‖ ^ 2 := by rw [← mul_assoc, hK2]

/-! ## fluxes -/

/-- flux of `c` (direction `μ`) through the top face of the box `w + [0,m)³`, divided by the face area. -/
noncomputable def flx (m : ℕ) (c : Bond L → SuTwo) (w : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (((m : ℝ) ^ 2)⁻¹) • ∑ u ∈ face m μ, c (w + off L u + (m - 1) • eU L μ, μ)

/-- the flux averaged over the `n³` translates of the box. -/
noncomputable def Fl (n m : ℕ) (c : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ : Fin 3) : SuTwo :=
  (((n : ℝ) ^ 3)⁻¹) • ∑ v ∈ cube n, flx m c (z + off L v) μ

/-- the box divergence identity: Σ over the box of `D* c` is the net inflow. -/
theorem box_div (c : Bond L → SuTwo) (m : ℕ) (hm : 0 < m) (w : PeriodicLatticeSite L) (μ : Fin 3) :
    ∑ u ∈ cube m, (c (w + off L u - eU L μ, μ) - c (w + off L u, μ))
      = ∑ u ∈ face m μ, (c (w + off L u - eU L μ, μ) - c (w + off L u + (m - 1) • eU L μ, μ)) := by
  rw [cube_split m μ]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hu0 : u μ = 0 := ((mem_face m μ u).mp hu).2
  set G : ℕ → SuTwo := fun t => c (w + off L u + t • eU L μ - eU L μ, μ) with hG
  have hstep : ∀ t ∈ Finset.range m,
      c (w + off L (Function.update u μ t) - eU L μ, μ) - c (w + off L (Function.update u μ t), μ) = G t - G (t + 1) := by
    intro t _
    simp only [hG, off_update u μ hu0, succ_nsmul]
    rw [show w + (off L u + t • eU L μ) - eU L μ = w + off L u + t • eU L μ - eU L μ by abel,
      show w + (off L u + t • eU L μ) = w + off L u + (t • eU L μ + eU L μ) - eU L μ by abel]
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub']
  simp only [hG, zero_smul, add_zero]
  congr 2
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [succ_nsmul, Nat.add_sub_cancel]
  abel

/-- **exact conservation** of the box fluxes for divergence-free `c`. -/
theorem flx_cons (c : BondFnL2 L) (hc : gradAdj (flatCfg : Cfg L) c = 0) (m : ℕ) (hm : 0 < m)
    (w : PeriodicLatticeSite L) :
    ∑ μ : Fin 3, (flx m c.ofLp (w - m • eU L μ) μ - flx m c.ofLp w μ) = 0 := by
  have hdiv : ∀ x, ∑ μ : Fin 3, (c.ofLp (x - eU L μ, μ) - c.ofLp (x, μ)) = 0 := by
    intro x
    have h := AdalyFormal.FlatCoercivity.gradAdj_flat_apply c x
    rw [← h, hc]; rfl
  have h0 : ∑ u ∈ cube m, ∑ μ : Fin 3, (c.ofLp (w + off L u - eU L μ, μ) - c.ofLp (w + off L u, μ)) = 0 :=
    Finset.sum_eq_zero (fun u _ => hdiv _)
  rw [Finset.sum_comm] at h0
  simp only [box_div c.ofLp m hm w] at h0
  have key : ∀ (μ : Fin 3) (u : Fin 3 → ℕ), w - m • eU L μ + off L u + (m - 1) • eU L μ = w + off L u - eU L μ := by
    intro μ u
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm', succ_nsmul, Nat.add_sub_cancel]
    abel
  have hterm : ∀ μ : Fin 3, flx m c.ofLp (w - m • eU L μ) μ - flx m c.ofLp w μ
      = (((m : ℝ) ^ 2)⁻¹) • ∑ u ∈ face m μ,
          (c.ofLp (w + off L u - eU L μ, μ) - c.ofLp (w + off L u + (m - 1) • eU L μ, μ)) := by
    intro μ
    unfold flx
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [key μ u]
  rw [Finset.sum_congr rfl (fun μ _ => hterm μ), ← Finset.smul_sum, h0, smul_zero]

theorem Fl_cons (c : BondFnL2 L) (hc : gradAdj (flatCfg : Cfg L) c = 0) (n m : ℕ) (hm : 0 < m)
    (z : PeriodicLatticeSite L) :
    ∑ μ : Fin 3, (Fl n m c.ofLp (z - m • eU L μ) μ - Fl n m c.ofLp z μ) = 0 := by
  unfold Fl
  simp only [← smul_sub, ← Finset.smul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have : ∀ v ∈ cube n, ∑ μ : Fin 3, (flx m c.ofLp (z - m • eU L μ + off L v) μ - flx m c.ofLp (z + off L v) μ) = 0 := by
    intro v _
    have h := flx_cons c hc m hm (z + off L v)
    rw [← h]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [show z - m • eU L μ + off L v = z + off L v - m • eU L μ by abel]
  rw [Finset.sum_eq_zero this, smul_zero]

#print axioms mem_face
#print axioms cube_split
#print axioms card_face
#print axioms cube_decomp
#print axioms face_decomp
#print axioms off_update
#print axioms add_off_val
#print axioms iota_eq_off
#print axioms block_cube
#print axioms fit_of_lat
#print axioms tiling
#print axioms onLat_add_iff
#print axioms onLat_smul_eU
#print axioms onLat_neg
#print axioms lat_translate
#print axioms avg_sq_le
#print axioms box_div
#print axioms flx_cons
#print axioms Fl_cons

end AdalyFormal.LemIFlat
