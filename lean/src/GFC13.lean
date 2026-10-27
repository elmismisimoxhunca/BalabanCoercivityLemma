import GFC12

/-!
# GFC13 -- the test site field `wu` built from a cell vector `u`: eigen, block-mean-zero, and `Δ wu = w_{Δ u}`.
Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

/-- integer representative of a torus site -/
def xh (x : Site L) : Z3 := fun μ => ((x μ : ℕ) : ℤ)

theorem ιz_xh (x : Site L) : ιz L (xh x) = x := by
  funext μ
  apply Fin.ext
  have h := fmod_val (L μ + 1) (Nat.succ_pos _) (xh x μ)
  have h1 : xh x μ % ((L μ + 1 : ℕ) : ℤ) = xh x μ := Int.emod_eq_of_lt (by simp [xh]) (by
    simp only [xh]; exact_mod_cast (x μ).isLt)
  rw [h1] at h
  simp only [xh] at h
  exact_mod_cast h

theorem lift_sub (hn : 0 < n) (z : Fin 3 → ℂ) (v w : CV n) (x : Z3) :
    lift hn z (v - w) x = lift hn z v x - lift hn z w x := by
  unfold lift; simp [mul_sub]

/-- the site field attached to a cell vector -/
noncomputable def wu (hn : 0 < n) (z : Fin 3 → ℂ) (u : CV n) : TS L :=
  WithLp.toLp 2 (fun x => lift hn z u (xh x))

theorem wu_apply (hn : 0 < n) (z : Fin 3 → ℂ) (u : CV n) (x : Site L) : wu hn z u x = lift hn z u (xh x) := rfl

/-- periodicity of the lift under the full torus period, given `z_μ^{M_μ} = 1` -/
theorem wu_ιz (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (z : Fin 3 → Circle)
    (hzM : ∀ μ, ((z μ : Circle) : ℂ) ^ Mc L n μ = 1) (u : CV n) (y : Z3) :
    wu hn (fun μ => (z μ : ℂ)) u (ιz L y) = lift hn (fun μ => (z μ : ℂ)) u y := by
  rw [wu_apply]
  set q : Z3 := fun μ => y μ / ((L μ + 1 : ℕ) : ℤ) with hq
  have hy : y = xh (ιz L y) + (n : ℤ) • (fun μ => (Mc L n μ : ℤ) * q μ) := by
    funext μ
    have h := fmod_val (L μ + 1) (Nat.succ_pos _) (y μ)
    have h2 := Int.emod_add_mul_ediv (y μ) ((L μ + 1 : ℕ) : ℤ)
    have h3 := Mc_mul hdvd μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, xh]
    have h4 : (n : ℤ) * ((Mc L n μ : ℤ) * q μ) = ((L μ + 1 : ℕ) : ℤ) * q μ := by
      rw [← mul_assoc]; congr 1; exact_mod_cast h3
    have h' : (((ιz L y μ).val : ℕ) : ℤ) = y μ % ((L μ + 1 : ℕ) : ℤ) := h
    have h5 : q μ = y μ / ((L μ + 1 : ℕ) : ℤ) := rfl
    rw [h4, h', h5]
    linarith [h2]
  have hz0 : ∀ μ, ((z μ : Circle) : ℂ) ≠ 0 := z_ne z
  conv_rhs => rw [hy]
  rw [lift_qp hn hz0]
  have : phase (fun μ => (z μ : ℂ)) (fun μ => (Mc L n μ : ℤ) * q μ) = 1 := by
    unfold phase
    refine Finset.prod_eq_one (fun μ _ => ?_)
    rw [zpow_mul, zpow_natCast, hzM μ, one_zpow]
  rw [this, one_mul]


theorem wu_eig (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ)
    (hzM : ∀ μ, ((zOf χ μ : Circle) : ℂ) ^ Mc L n μ = 1) (u : CV n) :
    IsEigS n χ (wu hn (fun μ => ((zOf χ μ : Circle) : ℂ)) u) := by
  intro g x
  have hz0 := z_ne (zOf χ)
  have h1 : x + n • g = ιz L (xh x + (n : ℤ) • xh g) := by
    rw [ιz_add, natCast_zsmul, ιz_nsmul, ιz_xh, ιz_xh]
  rw [h1, wu_ιz hn hdvd (zOf χ) hzM, lift_qp hn hz0, wu_apply, ← chi_ιz, ιz_xh]

theorem sum_cell_eq_inner (u : CV n) : ∑ t : Cell n, u t = ⟪epsV n, u⟫ := by
  rw [PiLp.inner_apply]
  simp [epsV]

theorem wu_mem_Wc (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ)
    (hzM : ∀ μ, ((zOf χ μ : Circle) : ℂ) ^ Mc L n μ = 1) (u : CV n) (hu : ⟪epsV n, u⟫ = 0) :
    wu hn (fun μ => ((zOf χ μ : Circle) : ℂ)) u ∈ Wc (n := n) hdvd := by
  intro c hc
  have hz0 := z_ne (zOf χ)
  set q : Z3 := fun μ => (((c μ : ℕ) / n : ℕ) : ℤ) with hq
  have hxc : xh c = (n : ℤ) • q := by
    funext μ
    simp only [xh, Pi.smul_apply, smul_eq_mul, hq]
    have := hc μ
    obtain ⟨k, hk⟩ := this
    rw [hk, Nat.mul_div_cancel_left _ hn]
    push_cast; rfl
  have h1 : ∀ t : Cell n, c + ιc hdvd t = ιz L ((n : ℤ) • q + cc t) := by
    intro t
    rw [ιz_add, ← hxc, ιz_xh, ιz_cc hdvd]
  have h2 : ∀ t : Cell n, wu hn (fun μ => ((zOf χ μ : Circle) : ℂ)) u (c + ιc hdvd t)
      = phase (fun μ => ((zOf χ μ : Circle) : ℂ)) q * u t := by
    intro t
    rw [h1, wu_ιz hn hdvd (zOf χ) hzM, add_comm, lift_qp hn hz0, lift_cc]
  simp only [h2]
  rw [← Finset.mul_sum, sum_cell_eq_inner, hu, mul_zero]


theorem Lap_cell_apply (hn : 0 < n) (z : Fin 3 → Circle) (u : CV n) (t : Cell n) :
    (cellSym hn z).Lap u t = ∑ μ : Fin 3, (2 * u t - lift hn (fun μ => (z μ : ℂ)) u (cc t + ev μ)
      - lift hn (fun μ => (z μ : ℂ)) u (cc t - ev μ)) := by
  have hz0 := z_ne z
  unfold SymData.Lap
  rw [show (∑ μ, (cellSym hn z).Ds μ ((cellSym hn z).D μ u)) t = ∑ μ, ((cellSym hn z).Ds μ ((cellSym hn z).D μ u)) t from by
    simp [WithLp.ofLp_sum, Finset.sum_apply]]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  show ((Su hn z μ).symm ((Su hn z μ) u - u)) t - ((Su hn z μ) u - u) t = _
  rw [Su_symm_eq, shiftOp_apply, Su_eq_shiftOp, lift_sub, lift_shiftOp hn hz0]
  simp only [PiLp.sub_apply, shiftOp_apply, ← sub_eq_add_neg, sub_add_cancel, lift_cc]
  ring

theorem lapC_wu_cell (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ)
    (hzM : ∀ μ, ((zOf χ μ : Circle) : ℂ) ^ Mc L n μ = 1) (u : CV n) (t : Cell n) :
    lapC L (wu hn (fun μ => ((zOf χ μ : Circle) : ℂ)) u) (ιc hdvd t) = (cellSym hn (zOf χ)).Lap u t := by
  rw [lapC_apply, Lap_cell_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  have e0 : ιc hdvd t = ιz L (cc t) := (ιz_cc hdvd t).symm
  have e1 : ιz L (cc t) + eU L μ = ιz L (cc t + ev μ) := by rw [ιz_add, ιz_ev]
  have e2 : ιz L (cc t) - eU L μ = ιz L (cc t - ev μ) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ιz_add, ιz_neg, ιz_ev]
  rw [e0, e1, e2, wu_ιz hn hdvd (zOf χ) hzM, wu_ιz hn hdvd (zOf χ) hzM, wu_ιz hn hdvd (zOf χ) hzM, lift_cc]

end AdalyFormal.FlatCoercivity
