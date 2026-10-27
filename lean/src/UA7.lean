import UA6
import UA5

/-!
# UA7 -- the 3D IMS partition on the unit torus (lane m2_unit_20261014)

Torus `L` with `M ∣ L_μ + 1` and `2M ≤ L_μ + 1` (`K_μ = (L_μ+1)/M ≥ 2` cells per axis).  Index `m : Π μ, Fin K_μ`,
`hpart m x = Π_μ ψ_{m_μ}(x_μ)` (UA6).
* `hpart_sumsq` : `Σ_m hpart_m(x)² = 1`.
* `hpart_lip`   : `Σ_m (hpart_m(x+e_μ) − hpart_m(x))² ≤ (π/2M)²`.
* `hpart_reach` : `Σ_m (hpart_m(z) − hpart_m(x))² ≤ (n π/2M)²` if `z` is reached from `x` in `n` forward steps.
* `restrict` versions: replacing `hpart_m` by `0` outside an index set keeps `≤ 1`, the Lipschitz bounds, and `= 1` at every `x`
  all of whose active indices are kept.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement

variable {L : PeriodicLatticeExtent}

/-- the number of cells on axis `μ`. -/
def Kc (L : PeriodicLatticeExtent) (M : ℕ) (μ : Fin 3) : ℕ := (L μ + 1) / M

/-- the 3D partition function. -/
noncomputable def hpart (M : ℕ) (m : (μ : Fin 3) → Fin (Kc L M μ)) (x : PeriodicLatticeSite L) : ℝ :=
  ∏ μ : Fin 3, psi1 M (Kc L M μ) (m μ) (x μ).val

/-- the torus conditions of the partition. -/
def PartOK (L : PeriodicLatticeExtent) (M : ℕ) : Prop := 0 < M ∧ (∀ μ : Fin 3, M ∣ L μ + 1) ∧ ∀ μ : Fin 3, 2 * M ≤ L μ + 1

theorem Kc_mul {M : ℕ} (h : PartOK L M) (μ : Fin 3) : Kc L M μ * M = L μ + 1 := Nat.div_mul_cancel (h.2.1 μ)

theorem Kc_two {M : ℕ} (h : PartOK L M) (μ : Fin 3) : 2 ≤ Kc L M μ := by
  unfold Kc; rw [Nat.le_div_iff_mul_le h.1]; exact h.2.2 μ

theorem coord_lt {M : ℕ} (h : PartOK L M) (x : PeriodicLatticeSite L) (μ : Fin 3) : (x μ).val < Kc L M μ * M := by
  rw [Kc_mul h]; exact (x μ).isLt

/-- product of the per-axis sums over the product index. -/
theorem sum_prod_axes (M : ℕ) (f : (μ : Fin 3) → Fin (Kc L M μ) → ℝ) :
    ∑ m : (μ : Fin 3) → Fin (Kc L M μ), ∏ μ : Fin 3, f μ (m μ) = ∏ μ : Fin 3, ∑ j : Fin (Kc L M μ), f μ j := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem hpart_sumsq {M : ℕ} (h : PartOK L M) (x : PeriodicLatticeSite L) :
    ∑ m, hpart M m x ^ 2 = 1 := by
  unfold hpart
  simp_rw [← Finset.prod_pow]
  rw [sum_prod_axes M (fun μ j => psi1 M (Kc L M μ) j (x μ).val ^ 2)]
  refine Finset.prod_eq_one (fun μ _ => ?_)
  exact psi1_sumsq h.1 (Kc_two h μ) (coord_lt h x μ)

theorem shift_val_self {M : ℕ} (h : PartOK L M) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (Kc L M μ * M) := by
  rw [Kc_mul h]
  have hL : 1 ≤ L μ := by have := h.2.2 μ; have := h.1; omega
  rw [AdalyFormal.StatementLane2.shift_apply, if_pos rfl, AdalyFormal.StatementLane2.fin_succ_val μ hL]

theorem shift_val_ne (x : PeriodicLatticeSite L) {μ ν : Fin 3} (hν : ν ≠ μ) :
    (periodicLatticeShift x μ) ν = x ν := by
  rw [AdalyFormal.StatementLane2.shift_apply, if_neg hν]

theorem hpart_cross {M : ℕ} (h : PartOK L M) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ∑ m, hpart M m x * hpart M m (periodicLatticeShift x μ) = Real.cos (Real.pi / (2 * M)) := by
  unfold hpart
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_prod_axes M (fun ν j => psi1 M (Kc L M ν) j (x ν).val * psi1 M (Kc L M ν) j ((periodicLatticeShift x μ) ν).val)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ μ)]
  have h1 : ∑ j : Fin (Kc L M μ), psi1 M (Kc L M μ) j (x μ).val * psi1 M (Kc L M μ) j ((periodicLatticeShift x μ) μ).val
      = Real.cos (Real.pi / (2 * M)) := by
    rw [shift_val_self h]; exact psi1_cross h.1 (Kc_two h μ) (coord_lt h x μ)
  have h2 : ∏ ν ∈ Finset.univ.erase μ, ∑ j : Fin (Kc L M ν),
      psi1 M (Kc L M ν) j (x ν).val * psi1 M (Kc L M ν) j ((periodicLatticeShift x μ) ν).val = 1 := by
    refine Finset.prod_eq_one (fun ν hν => ?_)
    have hne : ν ≠ μ := Finset.ne_of_mem_erase hν
    rw [shift_val_ne x hne]
    simp_rw [← sq]
    exact psi1_sumsq h.1 (Kc_two h ν) (coord_lt h x ν)
  rw [h1, h2, mul_one]

theorem hpart_lip {M : ℕ} (h : PartOK L M) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ∑ m, (hpart M m (periodicLatticeShift x μ) - hpart M m x) ^ 2 ≤ (Real.pi / (2 * M)) ^ 2 := by
  have e : ∑ m, (hpart M m (periodicLatticeShift x μ) - hpart M m x) ^ 2
      = ∑ m, hpart M m (periodicLatticeShift x μ) ^ 2 + ∑ m, hpart M m x ^ 2
        - 2 * ∑ m, hpart M m x * hpart M m (periodicLatticeShift x μ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => by ring)
  rw [e, hpart_sumsq h, hpart_sumsq h, hpart_cross h]
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / (2 * M))
  nlinarith

/-! ## restriction to an index set -/

open Classical in
/-- `hpart` kept on the indices in `I`, `0` elsewhere. -/
noncomputable def hres (M : ℕ) (I : Set ((μ : Fin 3) → Fin (Kc L M μ))) (m : (μ : Fin 3) → Fin (Kc L M μ))
    (x : PeriodicLatticeSite L) : ℝ :=
  if m ∈ I then hpart M m x else 0

theorem hres_sq_le {M : ℕ} (h : PartOK L M) (I : Set ((μ : Fin 3) → Fin (Kc L M μ))) (x : PeriodicLatticeSite L) :
    ∑ m, hres M I m x ^ 2 ≤ 1 := by
  rw [← hpart_sumsq h x]
  refine Finset.sum_le_sum (fun m _ => ?_)
  unfold hres; split_ifs <;> simp [sq_nonneg]

theorem hres_sq_eq {M : ℕ} (h : PartOK L M) (I : Set ((μ : Fin 3) → Fin (Kc L M μ))) (x : PeriodicLatticeSite L)
    (hI : ∀ m, hpart M m x ≠ 0 → m ∈ I) : ∑ m, hres M I m x ^ 2 = 1 := by
  rw [← hpart_sumsq h x]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  unfold hres
  by_cases hm : m ∈ I
  · rw [if_pos hm]
  · rw [if_neg hm]
    have : hpart M m x = 0 := by by_contra hne; exact hm (hI m hne)
    rw [this]

theorem hres_diff_le (M : ℕ) (I : Set ((μ : Fin 3) → Fin (Kc L M μ))) (x y : PeriodicLatticeSite L) :
    ∑ m, (hres M I m y - hres M I m x) ^ 2 ≤ ∑ m, (hpart M m y - hpart M m x) ^ 2 := by
  refine Finset.sum_le_sum (fun m _ => ?_)
  unfold hres; split_ifs <;> simp [sq_nonneg]

/-! ## ℓ²-Lipschitz along forward paths -/

/-- the partition as a vector in `ℓ²(index)`. -/
noncomputable def hvec (M : ℕ) (x : PeriodicLatticeSite L) : EuclideanSpace ℝ ((μ : Fin 3) → Fin (Kc L M μ)) :=
  WithLp.toLp 2 (fun m => hpart M m x)

theorem hvec_dist_sq (M : ℕ) (x y : PeriodicLatticeSite L) :
    ‖hvec M y - hvec M x‖ ^ 2 = ∑ m, (hpart M m y - hpart M m x) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp [hvec, Real.norm_eq_abs, sq_abs]

theorem hvec_step {M : ℕ} (h : PartOK L M) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ‖hvec M (periodicLatticeShift x μ) - hvec M x‖ ≤ Real.pi / (2 * M) := by
  have h1 := hvec_dist_sq M x (periodicLatticeShift x μ)
  have h2 := hpart_lip h x μ
  have hp : 0 ≤ Real.pi / (2 * M) := by have := Real.pi_pos; positivity
  rw [← h1] at h2
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hp two_ne_zero |>.mp h2

theorem hpart_reach {M : ℕ} (h : PartOK L M) {n : ℕ} {x z : PeriodicLatticeSite L}
    (hr : AdalyFormal.DLayer.Reach n x z) :
    ∑ m, (hpart M m z - hpart M m x) ^ 2 ≤ ((n : ℝ) * (Real.pi / (2 * M))) ^ 2 := by
  have hp : 0 ≤ Real.pi / (2 * M) := by have := Real.pi_pos; positivity
  have key : ∀ (l : List (Fin 3)) (x : PeriodicLatticeSite L),
      ‖hvec M (l.foldl (fun w μ => periodicLatticeShift w μ) x) - hvec M x‖ ≤ l.length * (Real.pi / (2 * M)) := by
    intro l
    induction l with
    | nil => intro x; simp
    | cons μ rest ih =>
        intro x
        rw [List.foldl_cons, List.length_cons]
        have h1 := ih (periodicLatticeShift x μ)
        have h2 := hvec_step h x μ
        calc ‖hvec M (rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ)) - hvec M x‖
            ≤ ‖hvec M (rest.foldl (fun w μ => periodicLatticeShift w μ) (periodicLatticeShift x μ))
                - hvec M (periodicLatticeShift x μ)‖ + ‖hvec M (periodicLatticeShift x μ) - hvec M x‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ rest.length * (Real.pi / (2 * M)) + Real.pi / (2 * M) := add_le_add h1 h2
          _ = ((rest.length + 1 : ℕ) : ℝ) * (Real.pi / (2 * M)) := by push_cast; ring
  obtain ⟨l, hl, rfl⟩ := hr
  have h1 := key l x
  have h2 : (l.length : ℝ) * (Real.pi / (2 * M)) ≤ (n : ℝ) * (Real.pi / (2 * M)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hp
  have h3 := le_trans h1 h2
  rw [← hvec_dist_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.hpart_sumsq
#print axioms AdalyFormal.M2Unit.hpart_cross
#print axioms AdalyFormal.M2Unit.hpart_lip
#print axioms AdalyFormal.M2Unit.hres_sq_le
#print axioms AdalyFormal.M2Unit.hres_sq_eq
#print axioms AdalyFormal.M2Unit.hres_diff_le
#print axioms AdalyFormal.M2Unit.hpart_reach
