import RKL1
/-!
# RKL2 -- sup-norm bounds for the pieces of the decomposition (RKL1), at EVERY bond (truncated blocks included).

* `pathM_le`:  `‖pathM s f y p‖ ≤ |p| M`.
* `avgM_le`:   `‖avgM s ell f c‖ ≤ ell M`  (convex combination of straight lines of `ell` links).
* `Gs_le`:     `‖Gs s ell f z‖ ≤ 3(ell−1) M`.
* `grad_le`:   `‖grad s Λ b‖ ≤ 2K` if `‖Λ‖ ≤ K`.
* `Es_le`:     `‖Es s ell f c‖ ≤ (3(ell−1)²/ell) M`: the blocks of `c₋` and `c₊` (offset sets `O(c±)`) agree on every offset
  `m` with `m_β = 0` (`β = c.2`), so only the `(ell−1) ell²` offsets with `m_β ≠ 0` can differ, each staircase `≤ 3(ell−1)` links.
Kernel-checked; standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.RegBgKU
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.ClassPropagationUbar (card_stepBlockOf_le gammaPath_length_le)
open AdalyFormal.CurvBlock (pathM bondM loopM blkM off gamma_eq shift_ne)

variable {L : PeriodicLatticeExtent}

theorem frob_add (X Y : M2) : frobNorm (X + Y) ≤ frobNorm X + frobNorm Y :=
  AdalyFormal.Balaban.Bch2.frobNorm_add_le X Y
theorem frob_sub (X Y : M2) : frobNorm (X - Y) ≤ frobNorm X + frobNorm Y :=
  AdalyFormal.Balaban.RegularityGap.frobNorm_sub_le X Y
theorem frob_smul (r : ℝ) (X : M2) : frobNorm (r • X) = |r| * frobNorm X :=
  AdalyFormal.Balaban.Bch2.frobNorm_smul r X
theorem frob_sum {ι : Type*} (S : Finset ι) (f : ι → M2) : frobNorm (∑ i ∈ S, f i) ≤ ∑ i ∈ S, frobNorm (f i) :=
  AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sum_le S f

theorem pathM_le (s : ℕ) (f : Fld L) (M : ℝ) (hf : ∀ b, frobNorm (f b) ≤ M) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), frobNorm (pathM s f y p) ≤ (p.length : ℝ) * M := by
  intro p; induction p with
  | nil => intro y; simp [pathM, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
  | cons μ r ih =>
      intro y
      have h1 := frob_add (f (y, μ)) (pathM s f (coarseShift y s μ) r)
      have h2 := hf (y, μ); have h3 := ih (coarseShift y s μ)
      simp only [pathM, List.length_cons]; push_cast; linarith

theorem card_le_real (y : PeriodicLatticeSite L) {s ell : ℕ} (hs : 0 < s) :
    ((stepBlockOf y s ell).card : ℝ) ≤ (ell : ℝ) ^ 3 := by
  exact_mod_cast card_stepBlockOf_le y (ell := ell) hs

theorem avgM_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (f : Fld L) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ b, frobNorm (f b) ≤ M) (c : PeriodicLatticeEdge L) :
    frobNorm (avgM s ell f c) ≤ (ell : ℝ) * M := by
  have hl3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hcard := card_le_real c.1 (ell := ell) hs
  set w : ℝ := ((stepBlockOf c.1 s ell).card : ℝ) / (ell : ℝ) ^ 3 with hw
  have hw1 : w ≤ 1 := by rw [hw, div_le_one hl3]; exact hcard
  have hw0 : 0 ≤ w := by positivity
  have hb : frobNorm (bondM s ell f c) ≤ (ell : ℝ) * M := by
    have := pathM_le s f M hf (List.replicate ell c.2) c.1
    simpa [bondM, List.length_replicate] using this
  have hline : ∀ x, frobNorm (((ell : ℝ) ^ 3)⁻¹ • pathM s f x (List.replicate ell c.2))
      ≤ ((ell : ℝ) ^ 3)⁻¹ * ((ell : ℝ) * M) := by
    intro x
    rw [frob_smul, abs_of_nonneg (by positivity)]
    have := pathM_le s f M hf (List.replicate ell c.2) x
    rw [List.length_replicate] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hsum : frobNorm (∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℝ) ^ 3)⁻¹ • pathM s f x (List.replicate ell c.2))
      ≤ w * ((ell : ℝ) * M) := by
    refine (frob_sum _ _).trans ?_
    refine (Finset.sum_le_sum (fun x _ => hline x)).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hw]; field_simp
  unfold avgM
  refine (frob_add _ _).trans ?_
  rw [frob_smul, abs_of_nonneg (by linarith)]
  rw [← hw]
  have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℝ) ≤ 1 - w)
  nlinarith

theorem Gs_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (f : Fld L) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ b, frobNorm (f b) ≤ M) (z : PeriodicLatticeSite L) :
    frobNorm (Gs s ell f z) ≤ 3 * ((ell : ℝ) - 1) * M := by
  have hl3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hcard := card_le_real z (ell := ell) hs
  have hterm : ∀ x ∈ stepBlockOf z s ell, frobNorm (((ell : ℝ) ^ 3)⁻¹ • pathM s f z (coarseGammaPath s z x))
      ≤ ((ell : ℝ) ^ 3)⁻¹ * (3 * ((ell : ℝ) - 1) * M) := by
    intro x hx
    rw [frob_smul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((pathM_le s f M hf _ z).trans ?_) (by positivity)
    have hlen := gammaPath_length_le z x hs hx
    have : ((coarseGammaPath s z x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
      have h' : ((coarseGammaPath s z x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by exact_mod_cast hlen
      rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h'; simpa using h'
    exact mul_le_mul_of_nonneg_right this hM
  unfold Gs
  refine (frob_sum _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : 0 ≤ 3 * ((ell : ℝ) - 1) * M := by have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
                                              positivity
  calc ((stepBlockOf z s ell).card : ℝ) * (((ell : ℝ) ^ 3)⁻¹ * (3 * ((ell : ℝ) - 1) * M))
      ≤ (ell : ℝ) ^ 3 * (((ell : ℝ) ^ 3)⁻¹ * (3 * ((ell : ℝ) - 1) * M)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 3 * ((ell : ℝ) - 1) * M := by field_simp

theorem grad_le (s : ℕ) (Λ : PeriodicLatticeSite L → M2) (K : ℝ) (hΛ : ∀ z, frobNorm (Λ z) ≤ K)
    (b : PeriodicLatticeEdge L) : frobNorm (grad s Λ b) ≤ 2 * K := by
  unfold grad
  have := frob_sub (Λ b.1) (Λ (coarseShift b.1 s b.2))
  linarith [hΛ b.1, hΛ (coarseShift b.1 s b.2)]

/-! ### the mismatch term -/

/-- offset vector of `x` relative to `z` in stride units. -/
def omega (s : ℕ) (z x : PeriodicLatticeSite L) : Fin 3 → ℕ := fun σ => off z x σ / s

/-- the staircase with offset vector `m` (CMP95 (1.7) order 2,1,0, as `gamma_eq`). -/
def stair (m : Fin 3 → ℕ) : List (Fin 3) :=
  List.replicate (m 2) 2 ++ (List.replicate (m 1) 1 ++ List.replicate (m 0) 0)

theorem gamma_eq_stair (s : ℕ) (z x : PeriodicLatticeSite L) : coarseGammaPath s z x = stair (omega s z x) :=
  gamma_eq s z x

/-- offsets fitting below the upper coordinate boundary. -/
def fits (s : ℕ) (z : PeriodicLatticeSite L) (m : Fin 3 → ℕ) : Prop := ∀ σ, (z σ).val + s * m σ < L σ + 1

instance (s : ℕ) (z : PeriodicLatticeSite L) (m : Fin 3 → ℕ) : Decidable (fits s z m) := by
  unfold fits; infer_instance

/-- the offset box `[0,ell)^3`. -/
def box (ell : ℕ) : Finset (Fin 3 → ℕ) := Fintype.piFinset (fun _ => Finset.range ell)

theorem mem_box {ell : ℕ} {m : Fin 3 → ℕ} : m ∈ box ell ↔ ∀ σ, m σ < ell := by
  simp [box, Fintype.mem_piFinset]

theorem omega_facts (s ell : ℕ) (hs : 0 < s) (z x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf z s ell) :
    ∀ σ, (x σ).val = (z σ).val + s * omega s z x σ ∧ omega s z x σ < ell := by
  intro σ
  have h := (mem_stepBlockOf.mp hx) σ
  have hoff : off z x σ = (x σ).val - (z σ).val := by unfold off; rw [Fin.sub_val_of_le h.1]
  have hd : s * (off z x σ / s) = off z x σ := by rw [hoff]; exact Nat.mul_div_cancel' h.2.2
  refine ⟨?_, ?_⟩
  · unfold omega; rw [hd, hoff]; omega
  · unfold omega; rw [Nat.div_lt_iff_lt_mul hs, hoff]; have := h.2.1; rw [Nat.mul_comm] at this; omega

theorem image_omega (s ell : ℕ) (hs : 0 < s) (z : PeriodicLatticeSite L) :
    (stepBlockOf z s ell).image (omega s z) = (box ell).filter (fits s z) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_filter, mem_box]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := omega_facts s ell hs z x hx
    refine ⟨fun σ => (h σ).2, fun σ => ?_⟩
    rw [← (h σ).1]; exact (x σ).isLt
  · rintro ⟨hm, hfit⟩
    refine ⟨fun σ => ⟨(z σ).val + s * m σ, hfit σ⟩, ?_, ?_⟩
    · rw [mem_stepBlockOf]
      intro σ
      refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
      · show (z σ).val + s * m σ < (z σ).val + s * ell
        have := hm σ; have : s * m σ < s * ell := Nat.mul_lt_mul_of_pos_left this hs
        omega
      · show s ∣ (z σ).val + s * m σ - (z σ).val
        rw [Nat.add_sub_cancel_left]; exact Dvd.intro _ rfl
    · funext σ
      unfold omega off
      have hle : z σ ≤ (⟨(z σ).val + s * m σ, hfit σ⟩ : Fin (L σ + 1)) := by
        rw [Fin.le_def]; exact Nat.le_add_right _ _
      rw [Fin.sub_val_of_le hle]
      show ((z σ).val + s * m σ - (z σ).val) / s = m σ
      rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hs]

theorem omega_injOn (s ell : ℕ) (hs : 0 < s) (z : PeriodicLatticeSite L) :
    Set.InjOn (omega s z) (stepBlockOf z s ell) := by
  intro x hx x' hx' he
  have h := omega_facts s ell hs z x hx
  have h' := omega_facts s ell hs z x' hx'
  funext σ
  apply Fin.ext
  rw [(h σ).1, (h' σ).1, show omega s z x σ = omega s z x' σ from congrFun he σ]

/-- reindexing a block sum by offset vectors. -/
theorem sum_block_eq (s ell : ℕ) (hs : 0 < s) (z : PeriodicLatticeSite L) (F : (Fin 3 → ℕ) → M2) :
    ∑ x ∈ stepBlockOf z s ell, F (omega s z x) = ∑ m ∈ (box ell).filter (fits s z), F m := by
  rw [← image_omega s ell hs z, Finset.sum_image (omega_injOn s ell hs z)]

theorem fits_shift_iff (s n : ℕ) (z : PeriodicLatticeSite L) (β : Fin 3) (m : Fin 3 → ℕ) (hm : m β = 0) :
    fits s (coarseShift z n β) m ↔ fits s z m := by
  unfold fits
  refine forall_congr' (fun σ => ?_)
  by_cases h : σ = β
  · subst h; rw [hm, Nat.mul_zero]
    exact ⟨fun _ => by simpa using (z σ).isLt, fun _ => by simpa using (coarseShift z n σ σ).isLt⟩
  · rw [shift_ne z n h]

theorem stair_length_le (ell : ℕ) (hell : 0 < ell) (m : Fin 3 → ℕ) (hm : m ∈ box ell) :
    ((stair m).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
  have h := mem_box.mp hm
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have : (stair m).length = m 2 + (m 1 + m 0) := by simp [stair]
  rw [this]
  have e : ((m 2 + (m 1 + m 0) : ℕ) : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by exact_mod_cast (by omega)
  rw [Nat.cast_mul, Nat.cast_sub (by omega)] at e; simpa using e

theorem card_box_ne (ell : ℕ) (hell : 0 < ell) (β : Fin 3) :
    (((box ell).filter (fun m => m β ≠ 0)).card : ℝ) = ((ell : ℝ) - 1) * (ell : ℝ) ^ 2 := by
  have he : (box ell).filter (fun m => m β ≠ 0)
      = Fintype.piFinset (fun σ => if σ = β then (Finset.range ell).erase 0 else Finset.range ell) := by
    ext m
    simp only [Finset.mem_filter, mem_box, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ σ
      by_cases h : σ = β
      · subst h; simp [h2, h1 σ]
      · simp [h, h1 σ]
    · intro h
      refine ⟨fun σ => ?_, ?_⟩
      · have := h σ
        by_cases hσ : σ = β
        · simp only [hσ, if_true, Finset.mem_erase, Finset.mem_range] at this; subst hσ; exact this.2
        · simp only [hσ, if_false, Finset.mem_range] at this; exact this
      · have := h β; simp only [if_true, Finset.mem_erase] at this; exact this.1
  have hc : (((Finset.range ell).erase 0).card : ℝ) = (ell : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (by simp; omega), Finset.card_range, Nat.cast_sub hell]; simp
  rw [he, Fintype.card_piFinset, Fin.prod_univ_three]
  fin_cases β <;> simp <;> rw [hc] <;> ring

/-- **The mismatch bound.** -/
theorem Es_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (f : Fld L) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ b, frobNorm (f b) ≤ M) (c : PeriodicLatticeEdge L) :
    frobNorm (Es s ell f c) ≤ 3 * ((ell : ℝ) - 1) ^ 2 / ell * M := by
  have hl : (0 : ℝ) < ell := by exact_mod_cast hell
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  set cp := cPlusS s ell c with hcp
  have hcp' : cp = coarseShift c.1 (s * ell) c.2 := cPlusS_eq s ell c
  set w : ℝ := ((ell : ℝ) ^ 3)⁻¹
  set F : (Fin 3 → ℕ) → M2 := fun m => w • pathM s f cp (stair m) with hF
  have h1 : Gs s ell f cp = ∑ m ∈ (box ell).filter (fits s cp), F m := by
    unfold Gs
    rw [← sum_block_eq s ell hs cp F]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [gamma_eq_stair]
  have h2 : ∑ x ∈ stepBlockOf c.1 s ell, w • pathM s f cp (coarseGammaPath s c.1 x)
      = ∑ m ∈ (box ell).filter (fits s c.1), F m := by
    rw [← sum_block_eq s ell hs c.1 F]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [gamma_eq_stair]
  have hE : Es s ell f c = ∑ m ∈ box ell, ((if fits s cp m then F m else 0) - (if fits s c.1 m then F m else 0)) := by
    unfold Es; rw [← hcp, h1, h2, Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter]
  have hterm : ∀ m ∈ box ell, frobNorm ((if fits s cp m then F m else 0) - (if fits s c.1 m then F m else 0))
      ≤ if m c.2 ≠ 0 then w * (3 * ((ell : ℝ) - 1) * M) else 0 := by
    intro m hm
    have hFm : frobNorm (F m) ≤ w * (3 * ((ell : ℝ) - 1) * M) := by
      simp only [hF]; rw [frob_smul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ((pathM_le s f M hf _ cp).trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_right (stair_length_le ell hell m hm) hM
    by_cases hβ : m c.2 = 0
    · have hiff : fits s cp m ↔ fits s c.1 m := by rw [hcp']; exact fits_shift_iff s _ c.1 c.2 m hβ
      simp only [hβ, ne_eq, not_true_eq_false, if_false]
      by_cases hf1 : fits s c.1 m
      · rw [if_pos (hiff.mpr hf1), if_pos hf1, sub_self, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
      · rw [if_neg (fun h => hf1 (hiff.mp h)), if_neg hf1, sub_self, AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    · rw [if_pos hβ]
      have h0 : frobNorm (0 : M2) = 0 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
      by_cases ha : fits s cp m <;> by_cases hb : fits s c.1 m <;>
        simp only [ha, hb, if_true, if_false, sub_self, sub_zero, zero_sub,
          AdalyFormal.Balaban.RegularityGap.frobNorm_neg, h0] <;>
        first | exact hFm | positivity
  rw [hE]
  refine (frob_sum _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_box_ne ell hell c.2]
  simp only [w]; field_simp
  try ring

#print axioms avgM_le
#print axioms Gs_le
#print axioms grad_le
#print axioms Es_le

#print axioms pathM_le
#print axioms image_omega
#print axioms omega_injOn
#print axioms sum_block_eq
#print axioms fits_shift_iff
#print axioms stair_length_le
#print axioms card_box_ne
#print axioms card_le_real
#print axioms omega_facts
#print axioms gamma_eq_stair
#print axioms mem_box
end AdalyFormal.RegBgKU
