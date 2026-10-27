import GFC11

/-!
# GFC12 -- cell identities for eigen fields: the curl and mass terms.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

theorem ιz_neg (a : Z3) : ιz L (-a) = -ιz L a := by
  have h := ιz_add (L := L) a (-a)
  rw [add_neg_cancel, ιz_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- master identity: values of an eigen field at `ιc t + ιz a` are shifted cell vectors -/
theorem eig_master (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) (a : Z3) (ν : Fin 3) (t : Cell n) :
    A (ιc hdvd t + ιz L a, ν) = shiftOp hn (fun μ => ((zOf χ μ : Circle) : ℂ)) a (vOf hdvd A ν) t := by
  have h := lift_relation hn hdvd χ A (fun g x μ => hA g x μ) ν (cc t + a)
  rw [ιz_add, ιz_cc hdvd] at h
  rw [h]; rfl

theorem eig_shift (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) (μ ν : Fin 3) (t : Cell n) :
    A (ιc hdvd t + eU L μ, ν) = Su hn (zOf χ) μ (vOf hdvd A ν) t := by
  rw [← ιz_ev, eig_master hn hdvd χ A hA]; rfl

theorem eig_shift_neg (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) (μ ν : Fin 3) (t : Cell n) :
    A (ιc hdvd t - eU L μ, ν) = (Su hn (zOf χ) μ).symm (vOf hdvd A ν) t := by
  rw [sub_eq_add_neg, ← ιz_ev, ← ιz_neg, eig_master hn hdvd χ A hA, Su_symm_eq]

theorem eig_iter (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) (μ ν : Fin 3) (i : ℕ) (t : Cell n) :
    A (ιc hdvd t + i • eU L μ, ν) = ((Su hn (zOf χ) μ)^[i] (vOf hdvd A ν)) t := by
  rw [← ιz_ev, ← ιz_nsmul, eig_master hn hdvd χ A hA, Su_iter_eq]
  simp [natCast_zsmul]

theorem vOf_apply (hdvd : ∀ μ, n ∣ L μ + 1) (A : TB L) (μ : Fin 3) (t : Cell n) :
    vOf hdvd A μ t = A (ιc hdvd t, μ) := rfl

/-- the curl term -/
theorem L1_cell (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) :
    ‖L1 L A‖ ^ 2 = Mnum L n * g1 hn (zOf χ, fun μ => vOf hdvd A μ) := by
  have hE : IsEig n χ (L1 L A) := eig_of_equiv χ A hA (L1 L) (fun g A => L1_equiv g A)
  rw [normB_eig hn hdvd χ _ hE]
  unfold g1
  have key : ∀ μ ν, ∑ t : Cell n, ‖L1 L A (ιc hdvd t, μ, ν)‖ ^ 2
      = (1 / 2 : ℝ) * ‖(cellSym hn (zOf χ)).D μ (vOf hdvd A ν) - (cellSym hn (zOf χ)).D ν (vOf hdvd A μ)‖ ^ 2 := by
    intro μ ν
    rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [L1_apply, eig_shift hn hdvd χ A hA, eig_shift hn hdvd χ A hA]
    show ‖((1 / Real.sqrt 2 : ℝ) : ℂ) * _‖ ^ 2 = _
    rw [norm_mul]
    have h2 : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [mul_pow, h2]
    congr 2
    simp only [PiLp.sub_apply, SymData.D, cellSym, vOf_apply]
    ring
  rw [Fintype.sum_prod_type]
  simp only [key, ← Finset.mul_sum]


theorem Qm_explicit (hn : 0 < n) (z : Fin 3 → Circle) (μ : Fin 3) (x : CV n) :
    (cellSym hn z).Qm μ x = ∑ t : Cell n, ∑ i ∈ Finset.range n, ((Su hn z μ)^[i] x) t := by
  unfold SymData.Qm
  show ⟪epsV n, ∑ i ∈ Finset.range n, (Su hn z μ)^[i] x⟫ = _
  rw [PiLp.inner_apply]
  simp only [epsV, RCLike.inner_apply, map_one, one_mul, WithLp.ofLp_sum]
  simp [Finset.sum_apply]

def zeroC (hn : 0 < n) : Cell n := fun _ => ⟨0, hn⟩

theorem coarse_ιc (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (t : Cell n) :
    Coarse n (ιc hdvd t) ↔ t = zeroC hn := by
  constructor
  · intro h
    funext μ
    apply Fin.ext
    have := h μ
    simp only [ιc] at this
    exact Nat.eq_zero_of_dvd_of_lt this (t μ).isLt
  · rintro rfl μ
    simp [ιc, zeroC]

theorem ιc_zero (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) : ιc hdvd (zeroC hn) = (0 : Site L) := by
  funext μ; apply Fin.ext; simp [ιc, zeroC]

/-- the mass term -/
theorem L2_cell (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) :
    ‖L2 hdvd A‖ ^ 2 = Mnum L n * g2 hn (zOf χ, fun μ => vOf hdvd A μ) := by
  have hE : IsEig n χ (L2 hdvd A) := eig_of_equiv χ A hA (L2 hdvd) (fun g A => L2_equiv hdvd g A)
  rw [normB_eig hn hdvd χ _ hE]
  unfold g2
  congr 1
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.sum_eq_single (zeroC hn)]
  · rw [L2_apply, if_pos ((coarse_ιc hn hdvd _).mpr rfl), ιc_zero]
    show ‖∑ t : Cell n, ∑ i ∈ Finset.range n, A (0 + ιc hdvd t + i • eU L μ, μ)‖ ^ 2 = ‖(cellSym hn (zOf χ)).Qm μ (vOf hdvd A μ)‖ ^ 2
    rw [Qm_explicit]
    congr 2
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [zero_add, eig_iter hn hdvd χ A hA]
  · intro t _ ht
    rw [L2_apply, if_neg (fun h => ht ((coarse_ιc hn hdvd t).mp h))]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

#print axioms L1_cell
#print axioms L2_cell

end AdalyFormal.FlatCoercivity
