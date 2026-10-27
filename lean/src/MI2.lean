import M1G4
import M1B
import MI1

/-!
# MI2 -- the bond partition, the W3 interface `PatchCoercive`, and the concrete W4 assembly (M1 lane E, 2026-10-13)

* `hbond p b` : the lane-B partition `hpart p` (G4) read at the endpoint of `b` that lies in `Ω₀` (tail if the tail is in `Ω₀`,
  else head).  `locB p A` : the bond field `b ↦ hbond p b • A b`, an element of `bondSupp` again.
* `sum_hbond_sq` : `Σ_p hbond p b ² = 1` for every bond with an endpoint in `Ω₀`; `wnorm_partition` :
  `Σ_p wnormSq (locB p A) = wnormSq A` for `A ∈ bondSupp`.
* `PatchCoercive cP` (THE W3 INTERFACE OF THIS LANE): on the REAL tower, for every patch `(j, w)` (`IsPatch`) and every
  `A ∈ bondSupp` whose nonzero bonds have an endpoint in `patch ell M κ c j w`: `cP · wnormSq A ≤ ⟪A, Ginv A⟫`.
* `GinvIMS ε e` (THE W1 OUTPUT FORM consumed here): `Σ_p ⟪locB p A, Ginv (locB p A)⟫ ≤ (1+ε)⟪A,Ginv A⟫ + e·wnormSq A`.
* **`ginv_weighted_coercive_of`** (W4): `GinvIMS ε e`, `PatchCoercive cP`, `0 ≤ ε` ⇒
  `((cP − e)/(1+ε)) · wnormSq A ≤ ⟪A, Ginv A⟫` for every `A ∈ bondSupp`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1

open Classical

section
variable {L : PeriodicLatticeExtent}

/-- the partition read on a bond: at the tail if the tail is in `Ω₀`, else at the head. -/
noncomputable def hbond (ell M k κ c : ℕ) (S : Tower L) (p : Fin (k + 1) × PeriodicLatticeSite L) (b : Bond L) : ℝ :=
  if b.1 ∈ S.Om 0 then hpart ell M k κ c S p b.1 else hpart ell M k κ c S p (periodicLatticeShift b.1 b.2)

theorem hbond_nonneg (ell M k κ c : ℕ) (S : Tower L) (p : Fin (k + 1) × PeriodicLatticeSite L) (b : Bond L) :
    0 ≤ hbond ell M k κ c S p b := by
  unfold hbond; split_ifs
  · exact hpart_nonneg _ _
  · exact hpart_nonneg _ _

/-- `Σ_p hbond_p(b)² = 1` on bonds with an endpoint in `Ω₀`. -/
theorem sum_hbond_sq {ell M k κ c : ℕ} {S : Tower L} (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    {b : Bond L} (hb : b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0) :
    ∑ p, hbond ell M k κ c S p b ^ 2 = 1 := by
  by_cases h1 : b.1 ∈ S.Om 0
  · simp only [hbond, if_pos h1]
    exact sum_hpart_sq hc hκ hM hell h1
  · have h2 : periodicLatticeShift b.1 b.2 ∈ S.Om 0 := hb.resolve_left h1
    simp only [hbond, if_neg h1]
    exact sum_hpart_sq hc hκ hM hell h2

/-- support of `hbond`: if `hbond p b ≠ 0` then `p` is a patch containing an endpoint of `b`. -/
theorem hbond_supp {ell M k κ c : ℕ} {S : Tower L} (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    {p : Fin (k + 1) × PeriodicLatticeSite L} {b : Bond L} (h : hbond ell M k κ c S p b ≠ 0) :
    IsPatch ell M k κ S p.1.val p.2 ∧
      (b.1 ∈ patch ell M κ c p.1.val p.2 ∨ periodicLatticeShift b.1 b.2 ∈ patch ell M κ c p.1.val p.2) := by
  unfold hbond at h
  split_ifs at h with h1
  · have := hpart_supp hc hκ hM hell h
    simp only [patchesAt, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact ⟨this.1, Or.inl this.2⟩
  · have := hpart_supp hc hκ hM hell h
    simp only [patchesAt, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact ⟨this.1, Or.inr this.2⟩

/-- the localised bond field `b ↦ hbond p b • A b`. -/
noncomputable def locF (ell M k κ c : ℕ) (S : Tower L) (p : Fin (k + 1) × PeriodicLatticeSite L) (A : BondFnL2 L) :
    BondFnL2 L :=
  WithLp.toLp 2 (fun b => hbond ell M k κ c S p b • (WithLp.ofLp A) b)

theorem locF_apply (ell M k κ c : ℕ) (S : Tower L) (p : Fin (k + 1) × PeriodicLatticeSite L) (A : BondFnL2 L)
    (b : Bond L) : (WithLp.ofLp (locF ell M k κ c S p A)) b = hbond ell M k κ c S p b • (WithLp.ofLp A) b := rfl

/-- the weighted norm of a localised field. -/
theorem wnormSq_locF (ell M k κ c : ℕ) (S : Tower L) (p : Fin (k + 1) × PeriodicLatticeSite L) (A : BondFnL2 L) :
    wnormSq S ell k (locF ell M k κ c S p A)
      = ∑ b : Bond L, (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 2 * (hbond ell M k κ c S p b ^ 2 * ‖(WithLp.ofLp A) b‖ ^ 2) := by
  unfold wnormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [locF_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- **the weighted norm is partitioned**: `Σ_p wnormSq(h_p A) = wnormSq A` when `A` vanishes off the bonds of `Ω₀`. -/
theorem wnorm_partition {ell M k κ c : ℕ} {S : Tower L} (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    (A : BondFnL2 L) (hA : ∀ b : Bond L, ¬ (b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0) → (WithLp.ofLp A) b = 0) :
    ∑ p, wnormSq S ell k (locF ell M k κ c S p A) = wnormSq S ell k A := by
  simp only [wnormSq_locF]
  rw [Finset.sum_comm]
  unfold wnormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : b.1 ∈ S.Om 0 ∨ periodicLatticeShift b.1 b.2 ∈ S.Om 0
  · have h1 := sum_hbond_sq (k := k) (κ := κ) (M := M) (c := c) (S := S) hc hκ hM hell hb
    calc ∑ p, (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 2 * (hbond ell M k κ c S p b ^ 2 * ‖(WithLp.ofLp A) b‖ ^ 2)
        = (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 2 * ((∑ p, hbond ell M k κ c S p b ^ 2) * ‖(WithLp.ofLp A) b‖ ^ 2) := by
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = _ := by rw [h1, one_mul]
  · rw [hA b hb]; simp

end

/-! ## the genuine operator -/

section
variable (ell M k κ c : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu))
  (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

/-- membership of `locF` in `bondSupp`. -/
theorem locF_mem (p : Fin (k + 1) × PeriodicLatticeSite (scaleUp ell k Lu))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    locF ell M k κ c S p (A : BondFnL2 (scaleUp ell k Lu)) ∈ bondSupp (gparams ell k Lu hell S U a Lam).G := by
  intro b hb
  rw [locF_apply, A.2 b hb, smul_zero]

/-- the localisation map on `E = bondSupp`. -/
noncomputable def locB (p : Fin (k + 1) × PeriodicLatticeSite (scaleUp ell k Lu))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G) :=
  ⟨locF ell M k κ c S p (A : BondFnL2 (scaleUp ell k Lu)), locF_mem ell M k κ c Lu hell S U a Lam p A⟩

/-- the genuine `Ginv` form. -/
noncomputable def ginvForm (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) : ℝ :=
  ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫

/-- the bond weighted norm on `E`. -/
noncomputable def wN (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) : ℝ :=
  wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))

/-- **W3 interface (this lane's statement; lane D to match or to transfer).** -/
def PatchCoercive (cP : ℝ) : Prop :=
  ∀ (j : ℕ) (w : PeriodicLatticeSite (scaleUp ell k Lu)), IsPatch ell M k κ S j w →
    ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
      (∀ b : Bond (scaleUp ell k Lu), (WithLp.ofLp (A : BondFnL2 (scaleUp ell k Lu))) b ≠ 0 →
        b.1 ∈ patch ell M κ c j w ∨ periodicLatticeShift b.1 b.2 ∈ patch ell M κ c j w) →
      cP * wN ell k Lu hell S U a Lam A ≤ ginvForm ell k Lu hell S U a Lam A

/-- **W1 output form (first-order IMS upper bound for the genuine `Ginv`).** -/
def GinvIMS (ε e : ℝ) : Prop :=
  ∀ A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G),
    ∑ p, ginvForm ell k Lu hell S U a Lam (locB ell M k κ c Lu hell S U a Lam p A)
      ≤ (1 + ε) * ginvForm ell k Lu hell S U a Lam A + e * wN ell k Lu hell S U a Lam A

theorem ginvForm_zero : ginvForm ell k Lu hell S U a Lam 0 = 0 := by
  unfold ginvForm; simp

/-- `PatchCoercive` gives the per-patch inequality for every localised field. -/
theorem patch_of_PatchCoercive (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (cP : ℝ)
    (hP : PatchCoercive ell M k κ c Lu hell S U a Lam cP) (p : Fin (k + 1) × PeriodicLatticeSite (scaleUp ell k Lu))
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    cP * wN ell k Lu hell S U a Lam (locB ell M k κ c Lu hell S U a Lam p A)
      ≤ ginvForm ell k Lu hell S U a Lam (locB ell M k κ c Lu hell S U a Lam p A) := by
  by_cases hp : IsPatch ell M k κ S p.1.val p.2
  · refine hP p.1.val p.2 hp _ (fun b hb => ?_)
    have hne : hbond ell M k κ c S p b ≠ 0 := by
      intro h0; apply hb
      show (WithLp.ofLp (locF ell M k κ c S p _)) b = 0
      rw [locF_apply, h0, zero_smul]
    exact (hbond_supp hc hκ hM hell hne).2
  · -- not a patch: the partition function vanishes identically
    have h0 : locB ell M k κ c Lu hell S U a Lam p A = 0 := by
      apply Subtype.ext
      refine PiLp.ext (fun b => ?_)
      show (WithLp.ofLp (locF ell M k κ c S p _)) b = 0
      rw [locF_apply]
      have : hbond ell M k κ c S p b = 0 := by
        by_contra hne
        exact hp (hbond_supp hc hκ hM hell hne).1
      rw [this, zero_smul]
    rw [h0, ginvForm_zero]
    have : wN ell k Lu hell S U a Lam (0 : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) = 0 := by
      unfold wN wnormSq; simp
    rw [this, mul_zero]

/-- the weighted norm on `E` is partitioned by `locB`. -/
theorem wN_partition (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    ∑ p, wN ell k Lu hell S U a Lam (locB ell M k κ c Lu hell S U a Lam p A) = wN ell k Lu hell S U a Lam A := by
  unfold wN
  exact wnorm_partition hc hκ hM hell (A : BondFnL2 (scaleUp ell k Lu)) (fun b hb => A.2 b hb)

/-- **W4 `ginv_weighted_coercive` (assembly)**: first-order IMS (`GinvIMS ε e`, W1 form) + `PatchCoercive cP` (W3, real
tower) give the stratum-weighted coercivity of the genuine `Ginv` on `E = bondSupp`. -/
theorem ginv_weighted_coercive_of (hc : 5 ≤ c) (hκ : 0 < κ) (hM : 0 < M) (ε e cP : ℝ) (hε : 0 ≤ ε)
    (hims : GinvIMS ell M k κ c Lu hell S U a Lam ε e) (hP : PatchCoercive ell M k κ c Lu hell S U a Lam cP)
    (A : ↥(bondSupp (gparams ell k Lu hell S U a Lam).G)) :
    ((cP - e) / (1 + ε)) * wnormSq S ell k (A : BondFnL2 (scaleUp ell k Lu))
      ≤ ⟪A, (gparams ell k Lu hell S U a Lam).data.Ginv A⟫ :=
  ims_assembly_div (ginvForm ell k Lu hell S U a Lam) (wN ell k Lu hell S U a Lam)
    (locB ell M k κ c Lu hell S U a Lam) (wN_partition ell M k κ c Lu hell S U a Lam hc hκ hM) cP ε e hε hims
    (patch_of_PatchCoercive ell M k κ c Lu hell S U a Lam hc hκ hM cP hP) A

end

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.hbond_nonneg
#print axioms AdalyFormal.M1IMS.sum_hbond_sq
#print axioms AdalyFormal.M1IMS.hbond_supp
#print axioms AdalyFormal.M1IMS.locF_apply
#print axioms AdalyFormal.M1IMS.wnormSq_locF
#print axioms AdalyFormal.M1IMS.wnorm_partition
#print axioms AdalyFormal.M1IMS.locF_mem
#print axioms AdalyFormal.M1IMS.ginvForm_zero
#print axioms AdalyFormal.M1IMS.patch_of_PatchCoercive
#print axioms AdalyFormal.M1IMS.wN_partition
#print axioms AdalyFormal.M1IMS.ginv_weighted_coercive_of
#print axioms AdalyFormal.M1IMS.hbond
#print axioms AdalyFormal.M1IMS.locF
#print axioms AdalyFormal.M1IMS.locB
#print axioms AdalyFormal.M1IMS.ginvForm
#print axioms AdalyFormal.M1IMS.wN
#print axioms AdalyFormal.M1IMS.PatchCoercive
#print axioms AdalyFormal.M1IMS.GinvIMS
