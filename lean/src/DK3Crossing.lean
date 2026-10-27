import DK3Scales
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace HConstruction.DK3
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.QcEquation (blockCorner blockCorner_mem blockCorner_val)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
attribute [local irreducible] blockOf CoarseLattice staircasePath axisSegment

/-- The source's distinguished crossing bond in EACH next-scale block. -/
def crossingBond (c : CoarseBond unitL 2) : Bond unitL :=
  (periodicLatticeShift c.1.1 c.2,c.2)

def Transverse (x : US) (μ : Fin 3) : Prop := ∀ ν, ν ≠ μ → (x ν).val % 2 = 0

def Crossing (b : Bond unitL) : Prop := (b.1 b.2).val % 2 = 1 ∧ Transverse b.1 b.2

instance (x : US) (μ : Fin 3) : Decidable (Transverse x μ) := inferInstanceAs
  (Decidable (∀ ν, ν ≠ μ → (x ν).val % 2 = 0))
instance (b : Bond unitL) : Decidable (Crossing b) := inferInstanceAs
  (Decidable ((b.1 b.2).val % 2 = 1 ∧ Transverse b.1 b.2))

def outputOf (b : Bond unitL) : CoarseBond unitL 2 :=
  (⟨blockCorner 2 b.1,blockCorner_mem b.1⟩,b.2)

theorem shift_self_val (x : US) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val+1)%32 := by
  simp only [periodicLatticeShift,Function.update_self,Fin.val_add]
  rfl

theorem transverse_shift (x : US) (μ : Fin 3) :
    Transverse (periodicLatticeShift x μ) μ ↔ Transverse x μ := by
  constructor
  · intro h ν hn
    have hh := h ν hn
    simpa only [periodicLatticeShift,Function.update_of_ne hn] using hh
  · intro h ν hn
    simpa only [periodicLatticeShift,Function.update_of_ne hn] using h ν hn

theorem center_mem (y : US) : y ∈ blockOf y 2 := by
  apply mem_blockOf.mpr
  intro μ
  omega

theorem crossing_mem (c : CoarseBond unitL 2) :
    (crossingBond c).1 ∈ blockOf c.1.1 2 := by
  apply mem_blockOf.mpr
  intro ν
  by_cases h : ν = c.2
  · subst ν
    have he := mem_CoarseLattice.mp c.1.2 c.2
    have hl : (c.1.1 c.2).val < 32 := (c.1.1 c.2).isLt
    change (c.1.1 c.2).val ≤ ((periodicLatticeShift c.1.1 c.2) c.2).val ∧
      ((periodicLatticeShift c.1.1 c.2) c.2).val < (c.1.1 c.2).val+2
    rw [shift_self_val,Nat.mod_eq_of_lt (show (c.1.1 c.2).val+1 < 32 by omega)]
    omega
  · simpa only [crossingBond,periodicLatticeShift,Function.update_of_ne h]
      using mem_blockOf.mp (center_mem c.1.1) ν

theorem crossing_is_crossing (c : CoarseBond unitL 2) : Crossing (crossingBond c) := by
  refine ⟨?_,?_⟩
  · change ((periodicLatticeShift c.1.1 c.2) c.2).val % 2 = 1
    have he := mem_CoarseLattice.mp c.1.2 c.2
    have hl : (c.1.1 c.2).val < 32 := (c.1.1 c.2).isLt
    rw [shift_self_val,Nat.mod_eq_of_lt (show (c.1.1 c.2).val+1 < 32 by omega)]
    omega
  · apply (transverse_shift _ _).mpr
    exact fun ν _ => mem_CoarseLattice.mp c.1.2 ν

theorem output_crossing (c : CoarseBond unitL 2) : outputOf (crossingBond c) = c := by
  apply Prod.ext
  · apply Subtype.ext
    exact AdalyFormal.Balaban.QcEquation.blockCorner_of_mem_blockOf c.1.2 (crossing_mem c)
  · rfl

theorem crossing_output (b : Bond unitL) (hb : Crossing b) : crossingBond (outputOf b) = b := by
  apply Prod.ext
  · funext ν
    apply Fin.ext
    by_cases h : ν = b.2
    · subst ν
      change ((periodicLatticeShift (blockCorner 2 b.1) b.2) b.2).val = _
      rw [shift_self_val,blockCorner_val]
      have hlt : (b.1 b.2).val < 32 := (b.1 b.2).isLt
      have hp := hb.1
      have hv : (b.1 b.2).val - (b.1 b.2).val%2+1 = (b.1 b.2).val := by omega
      rw [hv,Nat.mod_eq_of_lt hlt]
    · change ((periodicLatticeShift (blockCorner 2 b.1) b.2) ν).val = _
      rw [periodicLatticeShift,Function.update_of_ne h,blockCorner_val]
      have hp := hb.2 ν h
      omega
  · rfl

theorem crossing_ne_center (c : CoarseBond unitL 2) : (crossingBond c).1 ≠ c.1.1 := by
  intro h
  have hp := (crossing_is_crossing c).1
  change (((crossingBond c).1) c.2).val % 2 = 1 at hp
  rw [h,mem_CoarseLattice.mp c.1.2 c.2] at hp
  omega

/-- Exactly two longitudinal starts hit the distinguished crossing, independently
of the number of next-scale blocks. -/
theorem transverse_filter (c : CoarseBond unitL 2) :
    (blockOf c.1.1 2).filter (fun x => Transverse x c.2) =
      {c.1.1,(crossingBond c).1} := by
  ext x
  simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hx,ht⟩
    have hμ := mem_blockOf.mp hx c.2
    have hc := mem_CoarseLattice.mp c.1.2 c.2
    by_cases h : (x c.2).val = (c.1.1 c.2).val
    · left
      funext ν
      apply Fin.ext
      by_cases hn : ν = c.2
      · subst ν; exact h
      · have hh := mem_blockOf.mp hx ν
        have h0 := mem_CoarseLattice.mp c.1.2 ν
        have h1 := ht ν hn
        omega
    · right
      funext ν
      apply Fin.ext
      by_cases hn : ν = c.2
      · subst ν
        change _ = ((periodicLatticeShift c.1.1 c.2) c.2).val
        rw [shift_self_val,Nat.mod_eq_of_lt (by have := (x c.2).isLt; change (x c.2).val < 32 at this; omega)]
        omega
      · change _ = ((periodicLatticeShift c.1.1 c.2) ν).val
        rw [periodicLatticeShift,Function.update_of_ne hn]
        have hh := mem_blockOf.mp hx ν
        have h0 := mem_CoarseLattice.mp c.1.2 ν
        have h1 := ht ν hn
        omega
  · rintro (rfl|rfl)
    · exact ⟨center_mem _,fun ν _ => mem_CoarseLattice.mp c.1.2 ν⟩
    · exact ⟨crossing_mem c,(crossing_is_crossing c).2⟩

/-- Actual axial-tree edges lie in the first layer in their own direction. -/
theorem axial_even (y : US) (hy : y ∈ CoarseLattice unitL 2)
    (x : US) (hx : x ∈ blockOf y 2) (b : Bond unitL) (hb : b ∈ staircasePath y x) :
    (b.1 b.2).val % 2 = 0 := by
  have hw (ν : Fin 3) : min (y ν).val (x ν).val = (y ν).val ∧
      max (y ν).val (x ν).val = (x ν).val := by
    have h := mem_blockOf.mp hx ν
    omega
  rw [staircasePath,Finset.mem_union,Finset.mem_union] at hb
  rcases hb with (hb|hb)|hb
  all_goals
    rw [mem_axisSegment] at hb
    rcases hb with ⟨hd,_,hl,hu⟩
    rw [hd]
    rw [(hw _).1] at hl
    rw [(hw _).2] at hu
    have hx' := mem_blockOf.mp hx b.2
    have hy' := mem_CoarseLattice.mp hy b.2
    rw [hd] at hx' hy'
    omega

theorem crossing_off_axial (y : US) (hy : y ∈ CoarseLattice unitL 2)
    (x : US) (hx : x ∈ blockOf y 2) (b : Bond unitL) (hb : b ∈ staircasePath y x) :
    ¬ Crossing b := by
  intro h
  have := axial_even y hy x hx b hb
  have := h.1
  omega
end HConstruction.DK3
