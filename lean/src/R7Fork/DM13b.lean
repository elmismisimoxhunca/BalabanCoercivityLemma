import R7Fork.DM13a

/-!
# DM13b -- stratum blocks are classes; a block disjoint from `Om_m` is a union of stratum blocks of lower level; block-sum = sum of means;
connectedness of a box.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

section blocks
variable {L : PeriodicLatticeExtent}

theorem block_div_eq {n : ℕ} (hn : 0 < n) {y w : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L n)
    (hw : w ∈ blockOf y n) (ρ : Fin 3) : (w ρ).val / n = (y ρ).val / n := by
  have h := (mem_blockOf.mp hw) ρ
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) ρ)
  have h1 : (w ρ).val / n = q := by
    apply Nat.div_eq_of_lt_le
    · rw [mul_comm]; omega
    · rw [add_mul, one_mul, mul_comm]; omega
  have h2 : (y ρ).val / n = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
  rw [h1, h2]

theorem mem_block_of_div_eq {n : ℕ} (hn : 0 < n) {y v : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L n)
    (h : ∀ ρ, (v ρ).val / n = (y ρ).val / n) : v ∈ blockOf y n := by
  rw [mem_blockOf]
  intro ρ
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) ρ)
  have h2 : (y ρ).val / n = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
  have h3 := h ρ
  rw [h2] at h3
  have h4 := Nat.div_add_mod (v ρ).val n
  have h5 := Nat.mod_lt (v ρ).val hn
  rw [h3] at h4
  constructor <;> omega

theorem level_dvd {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {j : ℕ} (hj : j ≤ k) (ν : Fin 3) :
    ell ^ j ∣ L ν + 1 :=
  Dvd.dvd.trans (Dvd.intro_left M rfl) (hS.2.2.1 j hj ν)

/-- stratum blocks are equivalence classes -/
theorem stBlock_lev {ell M R k : ℕ} (hell : 0 < ell) {S : Tower L} (hS : Admissible ell M R k S)
    (x : PeriodicLatticeSite L) {w : PeriodicLatticeSite L} (hw : w ∈ stBlock ell S x) :
    lev S w = lev S x ∧ anc (ell ^ lev S w) w = anc (ell ^ lev S x) x := by
  have hx := lev_spec hS x
  set i := lev S x with hi
  have hn : 0 < ell ^ i := pow_pos hell i
  set y := anc (ell ^ i) x with hy
  have hwb : w ∈ blockOf y (ell ^ i) := hw
  have hyc : y ∈ CoarseLattice L (ell ^ i) := anc_coarse x
  have hdiv : ∀ ρ, ell ^ i ∣ (y ρ).val := fun ρ => ⟨_, anc_val _ _ _⟩
  have hyx : ∀ ρ, (y ρ).val / ell ^ i = (x ρ).val / ell ^ i := fun ρ => by
    rw [hy, anc_val]; exact Nat.mul_div_cancel_left _ hn
  have hwlev : IsLev S k w i := by
    refine ⟨hx.1, ?_, ?_⟩
    · rcases hx.2.1 with h0 | hxO
      · exact Or.inl h0
      · right
        have hyO : y ∈ S.Om i := by
          refine hS.2.2.2.1 i hx.1 x hxO y (fun ρ => ?_)
          unfold bigSide
          rw [blk_div, blk_div, hyx ρ]
        exact block_sub_Om hell hS hx.1 hdiv hyO hwb
    · intro hwO
      by_cases hk1 : i + 1 ≤ k
      · apply hx.2.2
        refine hS.2.2.2.1 (i + 1) hk1 w hwO x (fun ρ => ?_)
        unfold bigSide
        rw [blk_div, blk_div, pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
          block_div_eq hn hyc hwb ρ, hyx ρ]
      · have : S.Om (i + 1) = ∅ := hS.2.1 (i + 1) (by omega)
        rw [this] at hwO
        exact hwO
  have hl : lev S w = i := (isLev_unique hS.1 (lev_spec hS w) hwlev)
  refine ⟨hl, ?_⟩
  rw [hl]
  exact anc_eq_of_mem hn hyc hwb

theorem stBlock_eq {ell M R k : ℕ} (hell : 0 < ell) {S : Tower L} (hS : Admissible ell M R k S)
    {x w : PeriodicLatticeSite L} (hw : w ∈ stBlock ell S x) : stBlock ell S w = stBlock ell S x := by
  obtain ⟨h1, h2⟩ := stBlock_lev hell hS x hw
  unfold stBlock
  rw [h2, h1]

theorem self_mem_stBlock {ell : ℕ} (hell : 0 < ell) (S : Tower L) (x : PeriodicLatticeSite L) :
    x ∈ stBlock ell S x := mem_block_anc (pow_pos hell _) x

/-- a block disjoint from `Om_m` is a union of stratum blocks of lower level -/
theorem stBlock_sub_block {ell M R k m : ℕ} (hell : 0 < ell) {S : Tower L} (hS : Admissible ell M R k S)
    (hm : 1 ≤ m) {z : PeriodicLatticeSite L} (hz : z ∈ CoarseLattice L (ell ^ m))
    (hOm : ∀ w ∈ blockOf z (ell ^ m), w ∉ S.Om m) {w : PeriodicLatticeSite L} (hw : w ∈ blockOf z (ell ^ m)) :
    lev S w < m ∧ stBlock ell S w ⊆ blockOf z (ell ^ m) := by
  have hlev := lev_spec hS w
  have hlt : lev S w < m := by
    by_contra h
    push_neg at h
    have h0 : lev S w ≠ 0 := by omega
    exact hOm w hw (om_anti S hS.1 h (hlev.2.1.resolve_left h0))
  refine ⟨hlt, fun v hv => ?_⟩
  have hn : 0 < ell ^ m := pow_pos hell m
  have hni : 0 < ell ^ lev S w := pow_pos hell _
  apply mem_block_of_div_eq hn hz
  intro ρ
  have h1 := block_div_eq hni (anc_coarse w) hv ρ
  have h2 : (anc (ell ^ lev S w) w ρ).val / ell ^ lev S w = (w ρ).val / ell ^ lev S w := by
    rw [anc_val]; exact Nat.mul_div_cancel_left _ hni
  have h3 : (v ρ).val / ell ^ lev S w = (w ρ).val / ell ^ lev S w := by rw [h1, h2]
  have hpow : ell ^ m = ell ^ lev S w * ell ^ (m - lev S w) := by
    rw [← pow_add]; congr 1; omega
  have h4 : (v ρ).val / ell ^ m = (w ρ).val / ell ^ m := by
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h3]
  rw [h4]
  exact block_div_eq hn hz hw ρ

/-- the mean of `Θ` over the stratum block of `x` -/
noncomputable def meanB (ell : ℕ) (S : Tower L) (Θ : PeriodicLatticeSite L → SuTwo) (x : PeriodicLatticeSite L) : SuTwo :=
  (1 / ((ell ^ lev S x : ℕ) : ℝ) ^ 3) • ∑ v ∈ stBlock ell S x, Θ v

theorem sum_block_eq_sum_mean {ell M R k : ℕ} (hell : 0 < ell) {S : Tower L} (hS : Admissible ell M R k S)
    (Θ : PeriodicLatticeSite L → SuTwo) (X : Finset (PeriodicLatticeSite L))
    (hX : ∀ w ∈ X, stBlock ell S w ⊆ X) :
    ∑ w ∈ X, Θ w = ∑ w ∈ X, meanB ell S Θ w := by
  classical
  have hcard : ∀ w, (stBlock ell S w).card = (ell ^ lev S w) ^ 3 := fun w =>
    card_blockOf_of_coarse (level_dvd hS (lev_spec hS w).1) (anc_coarse w)
  have hpos : ∀ w, (0 : ℝ) < ((ell ^ lev S w : ℕ) : ℝ) := fun w => by
    have : 0 < ell ^ lev S w := pow_pos hell _
    exact_mod_cast this
  unfold meanB
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm' (t' := X) (s' := fun v => X.filter (fun w => v ∈ stBlock ell S w))]
  · refine Finset.sum_congr rfl (fun v hv => ?_)
    have hfil : X.filter (fun w => v ∈ stBlock ell S w) = stBlock ell S v := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hwX, hvw⟩
        rw [stBlock_eq hell hS hvw]
        exact self_mem_stBlock hell S w
      · intro hw
        refine ⟨hX v hv hw, ?_⟩
        rw [stBlock_eq hell hS hw]
        exact self_mem_stBlock hell S v
    rw [hfil]
    have hconst : ∀ w ∈ stBlock ell S v, (1 / ((ell ^ lev S w : ℕ) : ℝ) ^ 3) • Θ v
        = (1 / ((ell ^ lev S v : ℕ) : ℝ) ^ 3) • Θ v := by
      intro w hw
      rw [(stBlock_lev hell hS v hw).1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard v, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have h3 : ((ell ^ lev S v : ℕ) : ℝ) ^ 3 ≠ 0 := (pow_pos (hpos v) 3).ne'
    have : (((ell ^ lev S v) ^ 3 : ℕ) : ℝ) * (1 / ((ell ^ lev S v : ℕ) : ℝ) ^ 3) = 1 := by
      push_cast; field_simp
    rw [this, one_smul]
  · intro w v
    constructor
    · rintro ⟨hw, hv⟩
      exact ⟨Finset.mem_filter.mpr ⟨hw, hv⟩, hX w hw hv⟩
    · rintro ⟨hw, hv⟩
      exact ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩

/-- the anchor of a level-`i` site (`i >= 1`) is a centre of `Lambda_i` -/
theorem anc_Om {ell M R k : ℕ} (hell : 0 < ell) {S : Tower L} (hS : Admissible ell M R k S)
    {x : PeriodicLatticeSite L} {i : ℕ} (hx : IsLev S k x i) (hi1 : 1 ≤ i) :
    anc (ell ^ i) x ∈ S.Om i ∧ anc (ell ^ i) x ∉ S.Om (i + 1) := by
  have hn : 0 < ell ^ i := pow_pos hell i
  have hyx : ∀ ρ, ((anc (ell ^ i) x) ρ).val / ell ^ i = (x ρ).val / ell ^ i := fun ρ => by
    rw [anc_val]; exact Nat.mul_div_cancel_left _ hn
  have hxO : x ∈ S.Om i := hx.2.1.resolve_left (by omega)
  refine ⟨?_, ?_⟩
  · refine hS.2.2.2.1 i hx.1 x hxO _ (fun ρ => ?_)
    unfold bigSide
    rw [blk_div, blk_div, hyx ρ]
  · intro hyO
    by_cases hk1 : i + 1 ≤ k
    · apply hx.2.2
      refine hS.2.2.2.1 (i + 1) hk1 _ hyO x (fun ρ => ?_)
      unfold bigSide
      rw [blk_div, blk_div, pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hyx ρ]
    · have : S.Om (i + 1) = ∅ := hS.2.1 (i + 1) (by omega)
      rw [this] at hyO
      exact hyO

end blocks

end AdalyFormal.DirichletMono
