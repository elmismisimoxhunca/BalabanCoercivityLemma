import TL1n

/-!
# TL2a -- fibre counts of the covering projections and the lifted Hilbert spaces
-/
set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- uniform fibre cardinality -/
def FibreCount {Xt X : Type} [Fintype Xt] [Fintype X] [DecidableEq X] (π : Xt → X) (N : ℕ) : Prop :=
  ∀ x : X, (Finset.univ.filter (fun xt => π xt = x)).card = N

theorem sum_comp_fibre {Xt X : Type} [Fintype Xt] [Fintype X] [DecidableEq X] {π : Xt → X} {N : ℕ}
    (hπ : FibreCount π N) (F : X → ℝ) : ∑ xt, F (π xt) = N * ∑ x, F x := by
  have : ∑ xt, F (π xt) = ∑ x, ∑ xt ∈ Finset.univ.filter (fun xt => π xt = x), F (π xt) :=
    (Finset.sum_fiberwise (Finset.univ) π (fun xt => F (π xt))).symm
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_congr rfl (fun xt hxt => by rw [(Finset.mem_filter.mp hxt).2])]
  rw [Finset.sum_const, hπ x]
  simp

/-- the number of sheets -/
def sheets (Lt L : PeriodicLatticeExtent) : ℕ := ∏ μ : Fin 3, (Lt μ + 1) / (L μ + 1)

theorem card_fibre_coord (N m y : ℕ) (hm : 0 < m) (hmN : m ∣ N) (hy : y < m) :
    (Finset.univ.filter (fun a : Fin N => a.val % m = y)).card = N / m := by
  obtain ⟨n, rfl⟩ := hmN
  rw [Nat.mul_div_cancel_left _ hm]
  have : (Finset.univ.filter (fun a : Fin (m * n) => a.val % m = y)).card = (Finset.range n).card := by
    refine Finset.card_bij (fun (a : Fin (m * n)) _ => a.val / m) ?_ ?_ ?_
    · intro a _
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hm]
      have := a.isLt
      linarith [Nat.mul_comm m n]
    · intro a ha a' ha' h
      have h1 := (Finset.mem_filter.mp ha).2
      have h2 := (Finset.mem_filter.mp ha').2
      apply Fin.ext
      have e1 := Nat.div_add_mod a.val m
      have e2 := Nat.div_add_mod a'.val m
      rw [h1] at e1
      rw [h2] at e2
      rw [h] at e1
      omega
    · intro q hq
      have hq' := Finset.mem_range.mp hq
      refine ⟨⟨y + m * q, ?_⟩, ?_, ?_⟩
      · calc y + m * q < m + m * q := by omega
          _ = m * (q + 1) := by ring
          _ ≤ m * n := Nat.mul_le_mul_left m hq'
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
      · simp only
        rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hy, zero_add]
  rw [this, Finset.card_range]

theorem fibreCount_projS {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) :
    FibreCount (projS h) (sheets Lt L) := by
  intro y
  classical
  have : Finset.univ.filter (fun x : PeriodicLatticeSite Lt => projS h x = y) =
      Fintype.piFinset (fun μ : Fin 3 => Finset.univ.filter (fun a : Fin (Lt μ + 1) => a.val % (L μ + 1) = (y μ).val)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hx μ
      have := congrFun hx μ
      simpa [projS_val] using congrArg Fin.val this
    · intro hx
      funext μ
      exact Fin.ext (by simpa [projS_val] using hx μ)
  rw [this, Fintype.card_piFinset]
  unfold sheets
  refine Finset.prod_congr rfl (fun μ _ => ?_)
  exact card_fibre_coord (Lt μ + 1) (L μ + 1) (y μ).val (Nat.succ_pos _) (h μ) (y μ).isLt

section lift
open scoped RealInnerProductSpace
variable {Xt X : Type} [Fintype Xt] [Fintype X] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- pullback of a field along a map of index types -/
noncomputable def liftF (π : Xt → X) : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Xt => E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun xt => (WithLp.ofLp f) (π xt))
      map_add' := fun f g => by ext xt; simp
      map_smul' := fun c f => by ext xt; simp }

theorem liftF_apply (π : Xt → X) (f : PiLp 2 (fun _ : X => E)) (xt : Xt) : (liftF π f) xt = f (π xt) := rfl

theorem inner_liftF [DecidableEq X] {π : Xt → X} {N : ℕ} (hπ : FibreCount π N) (f g : PiLp 2 (fun _ : X => E)) :
    ⟪liftF π f, liftF π g⟫ = N * ⟪f, g⟫ := by
  simp only [PiLp.inner_apply, liftF_apply]
  exact sum_comp_fibre hπ (fun x => ⟪f x, g x⟫)

end lift

end AdalyFormal.Thin
