import DK2DepthFittedSurfaces

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedRepair

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov
  (coarsePathEndpoint coarseGammaPath coarseStraightSegment coarseCoordSteps)
open AdalyFormal.Balaban.QjComposite
  (stepBlockOf mem_stepBlockOf coarsePathEndpoint_coarseGammaPath)
open DepthUniformity.Strided (coarsePathEndpoint_coarseShift_S)
open Prop1.ScaleFittedProof (output_block_fits)

variable {L : PeriodicLatticeExtent}

/-- A common offset contour for all four blocks; no periodic gauge is constructed. -/
def offsetPath {ell : ℕ} (o : Fin 3 → Fin ell) : List (Fin 3) :=
  List.replicate (o 2).val 2 ++ (List.replicate (o 1).val 1 ++ List.replicate (o 0).val 0)

def offsetPoint (s : ℕ) (y : PeriodicLatticeSite L) {ell : ℕ} (o : Fin 3 → Fin ell) :
    PeriodicLatticeSite L := coarsePathEndpoint s y (offsetPath o)

private def fittedPoint (s ell : ℕ) (hs : 0 < s) (y : PeriodicLatticeSite L)
    (hfit : ∀ μ : Fin 3, (y μ).val + s*ell ≤ L μ+1) (o : Fin 3 → Fin ell) :
    PeriodicLatticeSite L := fun μ => ⟨(y μ).val+s*(o μ).val, by
      have hlt : s*(o μ).val < s*ell := Nat.mul_lt_mul_of_pos_left (o μ).isLt hs
      have h := hfit μ
      omega⟩

private theorem fittedPoint_mem (s ell : ℕ) (hs : 0 < s) (y : PeriodicLatticeSite L)
    (hfit : ∀ μ : Fin 3, (y μ).val + s*ell ≤ L μ+1) (o : Fin 3 → Fin ell) :
    fittedPoint s ell hs y hfit o ∈ stepBlockOf y s ell := by
  apply mem_stepBlockOf.mpr
  intro μ
  change (y μ).val ≤ (y μ).val+s*(o μ).val ∧
    (y μ).val+s*(o μ).val < (y μ).val+s*ell ∧
    s ∣ (y μ).val+s*(o μ).val-(y μ).val
  refine ⟨by omega, Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left (o μ).isLt hs) _, ?_⟩
  simp only [Nat.add_sub_cancel_left]
  exact dvd_mul_right s _

private theorem fittedPoint_path (s ell : ℕ) (hs : 0 < s) (y : PeriodicLatticeSite L)
    (hfit : ∀ μ : Fin 3, (y μ).val + s*ell ≤ L μ+1) (o : Fin 3 → Fin ell) :
    coarseGammaPath s y (fittedPoint s ell hs y hfit o) = offsetPath o := by
  let x := fittedPoint s ell hs y hfit o
  have hc (z : PeriodicLatticeSite L) (μ : Fin 3) (hz : z μ = y μ) :
      coarseCoordSteps s z x μ = (o μ).val := by
    unfold coarseCoordSteps
    rw [hz, Fin.sub_val_of_le (by change (y μ).val ≤ (y μ).val+s*(o μ).val; omega)]
    change ((y μ).val+s*(o μ).val-(y μ).val)/s = _
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hs]
  change coarseGammaPath s y x = _
  unfold coarseGammaPath coarseStraightSegment offsetPath
  rw [hc y 2 rfl,
    hc (Function.update y 2 (x 2)) 1 (by simp),
    hc (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 (by simp)]

private theorem offsetPoint_eq_fittedPoint (s ell : ℕ) (hs : 0 < s)
    (y : PeriodicLatticeSite L) (hfit : ∀ μ : Fin 3, (y μ).val+s*ell ≤ L μ+1)
    (o : Fin 3 → Fin ell) : offsetPoint s y o = fittedPoint s ell hs y hfit o := by
  unfold offsetPoint
  rw [← fittedPoint_path s ell hs y hfit o]
  apply coarsePathEndpoint_coarseGammaPath
  intro μ
  have h := mem_stepBlockOf.mp (fittedPoint_mem s ell hs y hfit o) μ
  exact ⟨h.1, h.2.2⟩

theorem offsetPoint_mem (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s*ell)) (o : Fin 3 → Fin ell) :
    offsetPoint s y o ∈ stepBlockOf y s ell := by
  rw [offsetPoint_eq_fittedPoint s ell hs y (output_block_fits s ell hd y hy)]
  exact fittedPoint_mem s ell hs y _ o

theorem offsetPoint_path (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s*ell)) (o : Fin 3 → Fin ell) :
    coarseGammaPath s y (offsetPoint s y o) = offsetPath o := by
  rw [offsetPoint_eq_fittedPoint s ell hs y (output_block_fits s ell hd y hy)]
  exact fittedPoint_path s ell hs y _ o

/-- Translation commutation holds even at wrapped output corners. -/
theorem offsetPoint_shift (s : ℕ) (y : PeriodicLatticeSite L) {ell : ℕ}
    (o : Fin 3 → Fin ell) (n : ℕ) (μ : Fin 3) :
    offsetPoint s (coarseShift y n μ) o = coarseShift (offsetPoint s y o) n μ :=
  coarsePathEndpoint_coarseShift_S s y n μ (offsetPath o)

theorem offsetPoint_injective (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s*ell)) :
    Function.Injective (offsetPoint s y (ell := ell)) := by
  intro o q hoq
  rw [offsetPoint_eq_fittedPoint s ell hs y (output_block_fits s ell hd y hy) o,
    offsetPoint_eq_fittedPoint s ell hs y (output_block_fits s ell hd y hy) q] at hoq
  funext μ
  apply Fin.ext
  have heq := congrArg (fun z : PeriodicLatticeSite L => (z μ).val) hoq
  change (y μ).val+s*(o μ).val = (y μ).val+s*(q μ).val at heq
  exact Nat.eq_of_mul_eq_mul_left hs (by omega)

theorem offsets_image (s ell : ℕ) (hs : 0 < s)
    (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s*ell)) :
    Finset.univ.image (offsetPoint s y (ell := ell)) = stepBlockOf y s ell := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hx
    exact offsetPoint_mem s ell hs hd y hy o
  · intro hx
    have hfit := output_block_fits s ell hd y hy
    let o : Fin 3 → Fin ell := fun μ => ⟨((x μ).val-(y μ).val)/s, by
      apply (Nat.div_lt_iff_lt_mul hs).mpr
      have hh := mem_stepBlockOf.mp hx μ
      rw [Nat.mul_comm]
      omega⟩
    refine Finset.mem_image.mpr ⟨o, Finset.mem_univ _, ?_⟩
    rw [offsetPoint_eq_fittedPoint s ell hs y hfit o]
    funext μ
    apply Fin.ext
    change (y μ).val+s*(((x μ).val-(y μ).val)/s) = (x μ).val
    have hh := mem_stepBlockOf.mp hx μ
    rw [Nat.mul_div_cancel' hh.2.2]
    omega

/-- Exact reindexing of each block into the SAME offset set; no missing sites,
no fixed-ell domain, no extra normalization assumption. -/
theorem sum_block_offsets {A : Type*} [AddCommMonoid A]
    (s ell : ℕ) (hs : 0 < s) (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s*ell))
    (F : PeriodicLatticeSite L → A) :
    ∑ x ∈ stepBlockOf y s ell, F x = ∑ o : Fin 3 → Fin ell, F (offsetPoint s y o) := by
  classical
  rw [← offsets_image s ell hs hd y hy, Finset.sum_image]
  intro a _ b _ hab
  exact offsetPoint_injective s ell hs hd y hy hab

end Prop1.ScaleFittedRepair

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedRepair.offsetPoint_mem,
      `Prop1.ScaleFittedRepair.offsetPoint_path,
      `Prop1.ScaleFittedRepair.offsetPoint_shift,
      `Prop1.ScaleFittedRepair.offsetPoint_injective,
      `Prop1.ScaleFittedRepair.offsets_image,
      `Prop1.ScaleFittedRepair.sum_block_offsets] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"FITTED_OFFSET_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "FITTED_OFFSETS_COMPLETE"
