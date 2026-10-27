import NuTwoUnc
import NsCvO1

/-!
# NuD0a -- the direction-0 staggered link family at the central uncovered bond (lane ncwdh_ell2_20261018)

`stag0Cfg xs t`: the direction-0 bond based at `x₀ = xs` carries `cartan (stagSign x * t)` (`stagSign x = (-1)^{x₁}`), every other bond is `1`.
At `ell = 2`, `xs = neC0 2 M R` (the lower endpoint of the central bond of the thin component): these links lie in no class cube
(`ne2_bond_uncovered`), so the family lies in the per-cube class for every `t` (`stag0_class`).  Plaquette weights: `cos (2t)` on the `(0,1)`-plaquettes at
`x₀ = xs`, `1` elsewhere (`holCos_stag0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.NoCover (perCube_one)

variable {L : PeriodicLatticeExtent}

/-- the imported lemmas carry an unused section variable `[CfData]`; any instance works. -/
local instance cfDefaultInst0 : CfData := ⟨10, le_refl 10⟩

/-- the direction-0 staggered link family. -/
noncomputable def stag0Cfg (xs : ℕ) (t : ℝ) : LinkCfg L :=
  fun e => if (e.1 0).val = xs ∧ e.2 = 0 then cartan (stagSign e.1 * t) else 1

theorem stag0Cfg_cartan (xs : ℕ) (t : ℝ) : CartanCfg (stag0Cfg (L := L) xs t) := by
  intro e
  unfold stag0Cfg
  split_ifs
  · exact cartan_isCartan _
  · unfold IsCartan; simp

theorem stag0Cfg_zero (xs : ℕ) :
    stag0Cfg (L := L) xs 0 = fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  funext e; unfold stag0Cfg; split_ifs
  · rw [mul_zero]; exact cartan_zero
  · rfl

theorem stagSign_shift_one (hN : 2 ∣ L 1 + 1) (x : PeriodicLatticeSite L) :
    stagSign (periodicLatticeShift x 1) = - stagSign x := by
  unfold stagSign
  have h1 : ((periodicLatticeShift x 1) 1).val = ((x 1).val + 1) % (L 1 + 1) := by
    simp [periodicLatticeShift, Fin.val_add]
  rw [h1]
  have : ((x 1).val + 1) % (L 1 + 1) % 2 = ((x 1).val + 1) % 2 := Nat.mod_mod_of_dvd _ hN
  rw [this]
  by_cases h : (x 1).val % 2 = 0
  · have : ((x 1).val + 1) % 2 ≠ 0 := by omega
    simp [h, this]
  · have : ((x 1).val + 1) % 2 = 0 := by omega
    simp [h, this]

/-- the layer plaquettes: the `(0,1)`-plaquettes at `x₀ = xs`. -/
def Pl0 (xs : ℕ) : Set (PeriodicLatticePlaquette L) := {p | p.2.1 = ((0 : Fin 3), (1 : Fin 3)) ∧ (p.1 0).val = xs}

theorem holonomy_stag0_01 (hN : 2 ∣ L 1 + 1) (xs : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((0 : Fin 3), (1 : Fin 3)).1 < ((0 : Fin 3), (1 : Fin 3)).2) :
    holonomyElem (stag0Cfg (L := L) xs t) (x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩) =
      cartan (if (x 0).val = xs then 2 * (stagSign x * t) else 0) := by
  unfold holonomyElem periodicPlaquetteHolonomy stag0Cfg
  have e : (periodicLatticeShift x 1) 0 = x 0 := by simp [periodicLatticeShift]
  have e1 := stagSign_shift_one hN x
  by_cases h2 : (x 0).val = xs
  · simp [e, h2, e1, cartan_inv, cartan_mul, cartan_zero]
    congr 1; ring
  · simp [e, h2, cartan_zero]

theorem holonomy_stag0_02 (xs : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((0 : Fin 3), (2 : Fin 3)).1 < ((0 : Fin 3), (2 : Fin 3)).2) :
    holonomyElem (stag0Cfg (L := L) xs t) (x, ⟨((0 : Fin 3), (2 : Fin 3)), h⟩) = cartan 0 := by
  unfold holonomyElem periodicPlaquetteHolonomy stag0Cfg
  have e : (periodicLatticeShift x 2) 0 = x 0 := by simp [periodicLatticeShift]
  have e1 : stagSign (periodicLatticeShift x 2) = stagSign x := stagSign_shift x 2 (by decide)
  by_cases h2 : (x 0).val = xs <;> simp [e, h2, e1, cartan_inv, cartan_mul, cartan_zero]

theorem holonomy_stag0_12 (xs : ℕ) (t : ℝ) (x : PeriodicLatticeSite L)
    (h : ((1 : Fin 3), (2 : Fin 3)).1 < ((1 : Fin 3), (2 : Fin 3)).2) :
    holonomyElem (stag0Cfg (L := L) xs t) (x, ⟨((1 : Fin 3), (2 : Fin 3)), h⟩) = cartan 0 := by
  unfold holonomyElem periodicPlaquetteHolonomy stag0Cfg
  simp [cartan_zero]

open Classical in
theorem holCos_stag0 (hN : 2 ∣ L 1 + 1) (xs : ℕ) (t : ℝ) (p : PeriodicLatticePlaquette L) :
    holCos (stag0Cfg (L := L) xs t) p = if p ∈ Pl0 xs then Real.cos (2 * t) else 1 := by
  obtain ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ := p
  have key : ∀ (μ ν : Fin 3), μ < ν → (μ = 0 ∧ ν = 1) ∨ (μ = 0 ∧ ν = 2) ∨ (μ = 1 ∧ ν = 2) := by decide
  rcases key μ ν h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [holCos_of_eq_cartan (holonomy_stag0_01 hN xs t x h)]
    by_cases h2 : (x 0).val = xs
    · have hm : (⟨x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩⟩ : PeriodicLatticePlaquette L) ∈ Pl0 xs := ⟨rfl, h2⟩
      rw [if_pos hm, if_pos h2]
      rcases stagSign_cases x with hs | hs <;> rw [hs]
      · rw [show 2 * ((1:ℝ) * t) = 2 * t by ring]
      · rw [show 2 * ((-1:ℝ) * t) = -(2 * t) by ring, Real.cos_neg]
    · have hm : (⟨x, ⟨((0 : Fin 3), (1 : Fin 3)), h⟩⟩ : PeriodicLatticePlaquette L) ∉ Pl0 xs := fun hh => h2 hh.2
      rw [if_neg hm, if_neg h2]; simp
  · rw [holCos_of_eq_cartan (holonomy_stag0_02 xs t x h)]
    have hm : (⟨x, ⟨((0 : Fin 3), (2 : Fin 3)), h⟩⟩ : PeriodicLatticePlaquette L) ∉ Pl0 xs := fun hh => by
      have := hh.1; simp at this
    rw [if_neg hm]; simp
  · rw [holCos_of_eq_cartan (holonomy_stag0_12 xs t x h)]
    have hm : (⟨x, ⟨((1 : Fin 3), (2 : Fin 3)), h⟩⟩ : PeriodicLatticePlaquette L) ∉ Pl0 xs := fun hh => by
      have := hh.1; simp at this
    rw [if_neg hm]; simp

end AdalyFormal.NcwdhTwo
