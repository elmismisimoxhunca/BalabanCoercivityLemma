import NuE3
import NuMin1
import NtCvOF8

/-!
# NuG1 -- the Z-block of the nested instance: invariant subspaces `W ⊆ E₀`, `Z ⊆ F` (lane ncwdh_ell2_20261018)

`WZ G`: the Z-fields of `E₀`; `ZF G`: the Z-rows.  `G1inv` preserves `WZ`, `Qs` maps `ZF` into `WZ`, `Q` maps `WZ` into `ZF` (all at the nested instance along `stag0Cfg`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

theorem zfield_smul (r : ℝ) (f : ℕ → ℝ) : (zfield (r • f) : BondFnL2 L) = r • zfield f := by
  refine PiLp.ext (fun b => ?_)
  show zfun (r • f) b = r • zfun f b
  unfold zfun
  split_ifs
  · exact dgS_smul r _
  · simp

theorem zfield_zero : (zfield (0 : ℕ → ℝ) : BondFnL2 L) = 0 := by
  refine PiLp.ext (fun b => ?_)
  show zfun 0 b = 0
  unfold zfun
  split_ifs
  · exact dgS_zero
  · rfl

theorem zrow_add (G : TowerGeom L) (ρ ρ' : ℕ → ℕ → ℝ) : zrow G (ρ + ρ') = zrow G ρ + zrow G ρ' := by
  refine PiLp.ext (fun p => ?_)
  show (if p.2.1.2 = 1 then dgS ((ρ + ρ') (p.1 : ℕ) (p.2.1.1 0).val) else 0) =
    (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) + (if p.2.1.2 = 1 then dgS (ρ' (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  split_ifs
  · exact dgS_add _ _
  · simp

theorem zrow_smul (G : TowerGeom L) (r : ℝ) (ρ : ℕ → ℕ → ℝ) : zrow G (r • ρ) = r • zrow G ρ := by
  refine PiLp.ext (fun p => ?_)
  show (if p.2.1.2 = 1 then dgS ((r • ρ) (p.1 : ℕ) (p.2.1.1 0).val) else 0) = r • (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  split_ifs
  · exact dgS_smul r _
  · simp

/-- the Z-fields of `E₀`. -/
def WZ (G : TowerGeom L) : Submodule ℝ ↥(bondSupp G) where
  carrier := {x | ∃ f : ℕ → ℝ, (x : BondFnL2 L) = zfield f}
  add_mem' := by
    rintro x y ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by rw [Submodule.coe_add, hf, hg, zfield_add]⟩
  zero_mem' := ⟨0, by simp [zfield_zero]⟩
  smul_mem' := by
    rintro r x ⟨f, hf⟩
    exact ⟨r • f, by rw [Submodule.coe_smul, hf, zfield_smul]⟩

/-- the Z-rows. -/
def ZF (G : TowerGeom L) : Submodule ℝ (FSp G) where
  carrier := {y | ∃ ρ : ℕ → ℕ → ℝ, y = zrow G ρ}
  add_mem' := by
    rintro x y ⟨ρ, rfl⟩ ⟨ρ', rfl⟩
    exact ⟨ρ + ρ', (zrow_add G ρ ρ').symm⟩
  zero_mem' := ⟨0, by
    refine PiLp.ext (fun p => ?_)
    show (0 : FSp G) p = (if p.2.1.2 = 1 then dgS ((0 : ℕ → ℕ → ℝ) (p.1 : ℕ) (p.2.1.1 0).val) else 0)
    split_ifs
    · exact (dgS_zero).symm
    · rfl⟩
  smul_mem' := by
    rintro r x ⟨ρ, rfl⟩
    exact ⟨r • ρ, (zrow_smul G r ρ).symm⟩

end

end AdalyFormal.NcwdhTwo
