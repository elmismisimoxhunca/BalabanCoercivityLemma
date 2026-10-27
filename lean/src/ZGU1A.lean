import ZXR2Close0d
import AdalyFormal.Balaban.ThirdLevelArrows
import AdalyFormal.Balaban.CoarseShiftCovariance

/-!
# GU1A -- the flat one-step jet `Dtot s ell` at ARBITRARY stride `s` (R2Flat5 proved stride 1 only)

`Dtot_flat_eq_s`: for `e` with base point in the `s*ell` coarse lattice on a torus with `s*ell ∣ L+1`,
`Dtot s ell e = Σ_{x ∈ B_s(e.1)} ell^{-3} • Σ_{i<ell} bondL (pathSite x e.2 (i*s), e.2)`.
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.GenuineU1

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice mem_CoarseLattice mem_blockOf
  coarseLattice_mem_fits)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf card_stepBlockOf)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)

variable {L : PeriodicLatticeExtent}

/-- the strided block of a stride-`s` coarse base point is the `s*ell`-block intersected with the
stride-`s` lattice -/
theorem stepBlock_eq_filter {y : PeriodicLatticeSite L} {s ell : ℕ} (hy : y ∈ CoarseLattice L s) :
    stepBlockOf y s ell = (blockOf y (s * ell)).filter (fun x => x ∈ CoarseLattice L s) := by
  ext x
  simp only [Finset.mem_filter, mem_stepBlockOf, mem_blockOf, mem_CoarseLattice]
  have hy' := mem_CoarseLattice.mp hy
  constructor
  · intro h
    refine ⟨fun μ => ⟨(h μ).1, (h μ).2.1⟩, fun μ => ?_⟩
    obtain ⟨c, hc⟩ := (h μ).2.2
    have h1 : (y μ).val = s * ((y μ).val / s) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hy' μ))).symm
    have h2 : (x μ).val = s * ((y μ).val / s + c) := by
      rw [Nat.mul_add, ← h1, ← hc]; have := (h μ).1; omega
    rw [h2]; exact Nat.mul_mod_right _ _
  · rintro ⟨h, hx⟩
    intro μ
    refine ⟨(h μ).1, (h μ).2, ?_⟩
    obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero (hx μ)
    obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero (hy' μ)
    exact ⟨a - b, by rw [Nat.mul_sub, ← ha, ← hb]⟩

/-- shifting by a multiple of `s` preserves `(·)_μ mod s` when `s ∣ L μ + 1` -/
theorem coarseShift_val_mod {s t : ℕ} (hst : s ∣ t) (μ : Fin 3) (hsM : s ∣ L μ + 1)
    (x : PeriodicLatticeSite L) :
    ((coarseShift x t μ) μ).val % s = (x μ).val % s := by
  rw [coarseShift_val_eq, Nat.mod_mod_of_dvd _ hsM, Nat.add_mod, Nat.mod_eq_zero_of_dvd hst, add_zero,
    Nat.mod_mod]

theorem mem_CL_shift_iff {s t : ℕ} (hst : s ∣ t) (μ : Fin 3) (hsM : ∀ ν, s ∣ L ν + 1)
    (x : PeriodicLatticeSite L) :
    coarseShift x t μ ∈ CoarseLattice L s ↔ x ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice, mem_CoarseLattice]
  constructor
  · intro h ν
    by_cases hν : ν = μ
    · subst hν; rw [← coarseShift_val_mod hst ν (hsM ν) x]; exact h ν
    · rw [← coarseShift_apply_ne x t μ ν hν]; exact h ν
  · intro h ν
    by_cases hν : ν = μ
    · subst hν; rw [coarseShift_val_mod hst ν (hsM ν) x]; exact h ν
    · rw [coarseShift_apply_ne x t μ ν hν]; exact h ν

theorem sum_stepBlock_shift {M : Type*} [AddCommMonoid M] (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (μ : Fin 3) (hdvd : ∀ ν, s * ell ∣ (L ν + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L (s * ell)) (f : PeriodicLatticeSite L → M) :
    ∑ x' ∈ stepBlockOf (coarseShift y (s * ell) μ) s ell, f x' =
      ∑ x ∈ stepBlockOf y s ell, f (coarseShift x (s * ell) μ) := by
  have hsdvd : ∀ ν, s ∣ L ν + 1 := fun ν => dvd_trans (dvd_mul_right s ell) (hdvd ν)
  have hpos : 0 < s * ell := Nat.mul_pos hs hell
  have hys : y ∈ CoarseLattice L s := by
    rw [mem_CoarseLattice] at hy ⊢
    intro ν
    exact Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_right s ell) (Nat.dvd_of_mod_eq_zero (hy ν)))
  have hy2 : coarseShift y (s * ell) μ ∈ CoarseLattice L (s * ell) :=
    AdalyFormal.Balaban.CoarseCurl.coarseShift_mem_coarseLattice hdvd hy μ
  have hy2s : coarseShift y (s * ell) μ ∈ CoarseLattice L s :=
    (mem_CL_shift_iff (dvd_mul_right s ell) μ hsdvd y).mpr hys
  classical
  rw [stepBlock_eq_filter hy2s, stepBlock_eq_filter hys, Finset.sum_filter, Finset.sum_filter,
    coarseShift_blockOf_eq_image hpos (hdvd μ) hy,
    Finset.sum_image (fun x _ x' _ h => coarseShift_injective (s * ell) μ h)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := mem_CL_shift_iff (dvd_mul_right s ell) μ hsdvd x
  by_cases hx : x ∈ CoarseLattice L s
  · rw [if_pos hx, if_pos (this.mpr hx)]
  · rw [if_neg hx, if_neg (fun h => hx (this.mp h))]

#print axioms stepBlock_eq_filter
#print axioms sum_stepBlock_shift

/-- first-order expansion of a straight stride-`s` line of `n` steps -/
theorem Tpath_replicate (s : ℕ) (μ : Fin 3) (n : ℕ) :
    ∀ y : PeriodicLatticeSite L, Tpath s y (List.replicate n μ)
      = ∑ i ∈ Finset.range n, bondL (pathSite y μ (i * s), μ) := by
  induction n with
  | zero => intro y; simp [Tpath]
  | succ n ih =>
      intro y
      rw [List.replicate_succ, Tpath, ih, Finset.sum_range_succ']
      have hp : ∀ i, pathSite (coarseShift y s μ) μ (i * s) = pathSite y μ ((i + 1) * s) := by
        intro i
        show (fun z => periodicLatticeShift z μ)^[i * s] ((fun z => periodicLatticeShift z μ)^[s] y) = _
        rw [← Function.iterate_add_apply, show (i + 1) * s = i * s + s by ring]
        rfl
      simp only [hp, Nat.zero_mul, pathSite_zero]
      exact add_comm _ _

theorem Ds_plus_eq_s (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hdvd : ∀ ν, s * ell ∣ (L ν + 1))
    (e : PeriodicLatticeEdge L) (he : e.1 ∈ CoarseLattice L (s * ell)) :
    Ds s ell (cPlusS s ell e)
      = ∑ x ∈ stepBlockOf e.1 s ell, Wt ell • Tpath s (cPlusS s ell e) (coarseGammaPath s e.1 x) := by
  have hcp : cPlusS s ell e = coarseShift e.1 (s * ell) e.2 := cPlusS_eq s ell e
  unfold Ds
  rw [hcp, sum_stepBlock_shift s ell hs hell e.2 hdvd he
    (fun x' => Wt ell • Tpath s (coarseShift e.1 (s * ell) e.2)
      (coarseGammaPath s (coarseShift e.1 (s * ell) e.2) x'))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [coarseGammaPath_congr s e.1 x (coarseShift e.1 (s * ell) e.2) (coarseShift x (s * ell) e.2)
    (fun ν => coarseShift_diff e.1 x (s * ell) e.2 ν)]

/-- **THE FLAT JET AT STRIDE `s`**: `Dtot s ell e a = Σ_{x∈B_s(e.1)} ell⁻³ Σ_{i<ell} a(x + i s e_μ, μ)`. -/
theorem Dtot_flat_eq_s (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hdvd : ∀ ν, s * ell ∣ (L ν + 1))
    (e : PeriodicLatticeEdge L) (he : e.1 ∈ CoarseLattice L (s * ell)) :
    Dtot s ell e = ∑ x ∈ stepBlockOf e.1 s ell,
      Wt ell • ∑ i ∈ Finset.range ell, bondL (pathSite x e.2 (i * s), e.2) := by
  have hcard : (stepBlockOf e.1 s ell).card = ell ^ 3 :=
    card_stepBlockOf e.1 s ell hs (coarseLattice_mem_fits hdvd he)
  have hW : Wt ell * ((ell : ℝ) ^ 3) = 1 := by
    unfold Wt
    have : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
    field_simp
  have hline : ∀ x : PeriodicLatticeSite L, Tpath s x (List.replicate ell e.2)
      = ∑ i ∈ Finset.range ell, bondL (pathSite x e.2 (i * s), e.2) :=
    fun x => Tpath_replicate s e.2 ell x
  unfold Dtot Davg Tloop
  rw [Ds_plus_eq_s s ell hs hell hdvd e he]
  unfold Ds
  simp only [smul_add, smul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    hcard, ← hline]
  have hc : ((ell ^ 3 : ℕ) • (Wt ell • Tpath s e.1 (List.replicate ell e.2)))
      = Tpath s e.1 (List.replicate ell e.2) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [mul_comm, hW, one_smul]
  rw [hc]
  abel

#print axioms Tpath_replicate
#print axioms Ds_plus_eq_s
#print axioms Dtot_flat_eq_s

end AdalyFormal.GenuineU1
