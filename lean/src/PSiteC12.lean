import PSiteC6

/-!
# SiteC12 -- LOCAL holonomy deviation: the staircase transport inside a block depends only on the links BASED at sites of the block.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage coarsePathHolonomy_cons coarsePathEndpoint_cons
  coarsePathEndpoint_append coarsePathHolonomy_append coarsePathEndpoint_replicate)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarsePathEndpoint coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

/-- the path (a list of directions, strided by `s`) from `y` only visits bases in `B` -/
def PathIn (B : Set (PeriodicLatticeSite L)) (s : ℕ) : PeriodicLatticeSite L → List (Fin 3) → Prop
  | _, [] => True
  | y, μ :: rest => y ∈ B ∧ PathIn B s (coarseShift y s μ) rest

theorem PathIn_append (B : Set (PeriodicLatticeSite L)) (s : ℕ) (y : PeriodicLatticeSite L) (p q : List (Fin 3)) :
    PathIn B s y (p ++ q) ↔ PathIn B s y p ∧ PathIn B s (coarsePathEndpoint s y p) q := by
  induction p generalizing y with
  | nil => simp [PathIn, coarsePathEndpoint]
  | cons μ rest ih =>
    simp only [List.cons_append, PathIn, coarsePathEndpoint_cons, ih]
    tauto

theorem hol_dev_local (B : Set (PeriodicLatticeSite L)) (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hV : ∀ z ∈ B, ∀ μ : Fin 3, frobNorm ((V (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), PathIn B s y p →
      frobNorm (((coarsePathHolonomy s V y p : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ (p.length : ℝ) * δ := by
  intro p
  induction p with
  | nil =>
    intro y _
    show frobNorm (((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ _
    rw [AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self, List.length_nil, Nat.cast_zero, zero_mul]
    exact le_of_eq AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  | cons μ rest ih =>
    intro y hy
    obtain ⟨hyB, hrest⟩ := hy
    show frobNorm (((V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ _
    refine le_trans (AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le _ _) ?_
    have h1 := hV y hyB μ
    have h2 := ih (coarseShift y s μ) hrest
    rw [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith


theorem coarseShift_val_ne' (z : PeriodicLatticeSite L) (a : ℕ) {μ ν : Fin 3} (h : ν ≠ μ) :
    (coarseShift z a μ ν).val = (z ν).val := by
  rw [coarseShift_apply_ne z a μ ν h]

/-- a straight strided segment inside the box `[y, y + m)` stays in the box -/
theorem PathIn_replicate_box (y : PeriodicLatticeSite L) (m s : ℕ) (hfit : ∀ μ, (y μ).val + m ≤ L μ + 1)
    (μ : Fin 3) :
    ∀ (n : ℕ) (z : PeriodicLatticeSite L), z ∈ blockOf y m → (z μ).val + s * n < (y μ).val + m →
      PathIn (↑(blockOf y m) : Set (PeriodicLatticeSite L)) s z (List.replicate n μ) := by
  intro n
  induction n with
  | zero => intro z _ _; trivial
  | succ n ih =>
    intro z hz hlt
    refine ⟨Finset.mem_coe.mpr hz, ?_⟩
    have hz' := mem_blockOf.mp hz
    have hval : (coarseShift z s μ μ).val = (z μ).val + s := by
      rw [coarseShift_val_eq]
      apply Nat.mod_eq_of_lt
      have := hfit μ
      have h2 : s * (n + 1) = s * n + s := by ring
      omega
    have hmem : coarseShift z s μ ∈ blockOf y m := by
      rw [mem_blockOf]
      intro ν
      by_cases hν : ν = μ
      · subst hν
        have h2 : s * (n + 1) = s * n + s := by ring
        have := (hz' ν).1
        constructor <;> omega
      · rw [coarseShift_val_ne' z s hν]
        exact hz' ν
    refine ih _ hmem ?_
    rw [hval]
    have h2 : s * (n + 1) = s * n + s := by ring
    omega


theorem coarseShift_val_lt (z : PeriodicLatticeSite L) (a : ℕ) (μ : Fin 3) (hlt : (z μ).val + a < L μ + 1) :
    (coarseShift z a μ μ).val = (z μ).val + a := by
  rw [coarseShift_val_eq]
  exact Nat.mod_eq_of_lt hlt

theorem fin3_cases (ν : Fin 3) : ν = 0 ∨ ν = 1 ∨ ν = 2 := by
  fin_cases ν <;> simp

theorem pathSite_eq_coarseShift (z : PeriodicLatticeSite L) (μ : Fin 3) (a : ℕ) :
    AdalyFormal.Balaban.QOne.pathSite z μ a = coarseShift z a μ := rfl

/-- THE STAIRCASE `y → x` STAYS INSIDE THE BIG BLOCK `blockOf y (s * ell)`. -/
theorem gammaPath_PathIn {y x : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s)
    (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1) (hx : x ∈ stepBlockOf y s ell) :
    PathIn (↑(blockOf y (s * ell)) : Set (PeriodicLatticeSite L)) s y (coarseGammaPath s y x) := by
  have hxm := mem_stepBlockOf.mp hx
  have hsteps : ∀ μ : Fin 3, s * ((x μ - y μ).val / s) = (x μ).val - (y μ).val := by
    intro μ
    have hle : y μ ≤ x μ := by rw [Fin.le_def]; exact (hxm μ).1
    have hval : (x μ - y μ).val = (x μ).val - (y μ).val := Fin.sub_val_of_le hle
    rw [hval]
    exact Nat.mul_div_cancel' (hxm μ).2.2
  have hyB : y ∈ blockOf y (s * ell) := by
    rw [mem_blockOf]; intro μ
    have := hxm μ
    constructor
    · exact le_refl _
    · have h1 : (y μ).val ≤ (x μ).val := this.1
      omega
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have hu1 : (Function.update y 2 (x 2)) 1 = y 1 := Function.update_of_ne h21.symm _ _
  have hv0 : (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 = y 0 := by
    rw [Function.update_of_ne h10.symm, Function.update_of_ne h20.symm]
  have hm1 : coarseCoordSteps s (Function.update y 2 (x 2)) x 1 = (x 1 - y 1).val / s := by
    show (x 1 - (Function.update y 2 (x 2)) 1).val / s = _
    rw [hu1]
  have hm0 : coarseCoordSteps s (Function.update (Function.update y 2 (x 2)) 1 (x 1)) x 0 = (x 0 - y 0).val / s := by
    show (x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val / s = _
    rw [hv0]
  unfold coarseGammaPath coarseStraightSegment
  rw [hm1, hm0]
  have hm2 : coarseCoordSteps s y x 2 = (x 2 - y 2).val / s := rfl
  rw [hm2]
  rw [PathIn_append]
  refine ⟨PathIn_replicate_box y (s * ell) s hfit 2 _ y hyB (by have := hsteps 2; have := hxm 2; omega), ?_⟩
  rw [coarsePathEndpoint_replicate, pathSite_eq_coarseShift]
  have hs2 := hsteps 2
  have hs1 := hsteps 1
  have hs0 := hsteps 0
  have hx2 := hxm 2
  have hx1 := hxm 1
  have hx0 := hxm 0
  have hxlt2 : (x 2).val < L 2 + 1 := (x 2).isLt
  have hxlt1 : (x 1).val < L 1 + 1 := (x 1).isLt
  have hxlt0 : (x 0).val < L 0 + 1 := (x 0).isLt
  -- z1: after the 2-segment
  have hz1_2 : (coarseShift y (s * ((x 2 - y 2).val / s)) 2 2).val = (x 2).val := by
    rw [coarseShift_val_lt _ _ _ (by omega)]; omega
  have hz1_1 : (coarseShift y (s * ((x 2 - y 2).val / s)) 2 1).val = (y 1).val :=
    coarseShift_val_ne' y _ h21.symm
  have hz1_0 : (coarseShift y (s * ((x 2 - y 2).val / s)) 2 0).val = (y 0).val :=
    coarseShift_val_ne' y _ h20.symm
  have hz1B : coarseShift y (s * ((x 2 - y 2).val / s)) 2 ∈ blockOf y (s * ell) := by
    rw [mem_blockOf]; intro ν
    rcases fin3_cases ν with rfl | rfl | rfl
    · rw [hz1_0]; have := (hxm 0).1; have := hx0.2.1; omega
    · rw [hz1_1]; have := hx1.2.1; omega
    · rw [hz1_2]; have := hx2.1; have := hx2.2.1; omega
  rw [PathIn_append]
  refine ⟨PathIn_replicate_box y (s * ell) s hfit 1 _ _ hz1B (by rw [hz1_1]; omega), ?_⟩
  rw [coarsePathEndpoint_replicate, pathSite_eq_coarseShift]
  have hz2_1 : (coarseShift (coarseShift y (s * ((x 2 - y 2).val / s)) 2) (s * ((x 1 - y 1).val / s)) 1 1).val = (x 1).val := by
    rw [coarseShift_val_lt _ _ _ (by rw [hz1_1]; omega), hz1_1]; omega
  have hz2_2 : (coarseShift (coarseShift y (s * ((x 2 - y 2).val / s)) 2) (s * ((x 1 - y 1).val / s)) 1 2).val = (x 2).val := by
    rw [coarseShift_val_ne' _ _ (by decide : (2 : Fin 3) ≠ 1), hz1_2]
  have hz2_0 : (coarseShift (coarseShift y (s * ((x 2 - y 2).val / s)) 2) (s * ((x 1 - y 1).val / s)) 1 0).val = (y 0).val := by
    rw [coarseShift_val_ne' _ _ (by decide : (0 : Fin 3) ≠ 1), hz1_0]
  have hz2B : coarseShift (coarseShift y (s * ((x 2 - y 2).val / s)) 2) (s * ((x 1 - y 1).val / s)) 1
      ∈ blockOf y (s * ell) := by
    rw [mem_blockOf]; intro ν
    rcases fin3_cases ν with rfl | rfl | rfl
    · rw [hz2_0]; have := hx0.2.1; omega
    · rw [hz2_1]; have := hx1.1; have := hx1.2.1; omega
    · rw [hz2_2]; have := hx2.1; have := hx2.2.1; omega
  exact PathIn_replicate_box y (s * ell) s hfit 0 _ _ hz2B (by rw [hz2_0]; omega)

end AdalyFormal.SiteCoercivity
