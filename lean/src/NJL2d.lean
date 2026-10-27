import NJL2c
import NJ6bSup

/-!
# NJL2d -- (volume-free L2, step 4) the offset set `D` and the FAMILY BOUND
`Σ_c Σ_{u∈B(c₋)} pathSum g (c₋ + a(u-c₋,μ)) (q(u-c₋,μ)) ≤ 3 ell³ m ‖g‖₁`  whenever every path `q(d,μ)` has length `≤ m`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)

variable {L : PeriodicLatticeExtent}

/-- offsets `d` with every coordinate `< ell`. -/
def Doff (L : PeriodicLatticeExtent) (ell : ℕ) : Finset (PeriodicLatticeSite L) :=
  Finset.univ.filter (fun d => ∀ ν, (d ν).val < ell)

theorem card_Doff_le (ell : ℕ) : (Doff L ell).card ≤ ell ^ 3 := by
  classical
  have h := Finset.card_le_card_of_injOn (fun d : PeriodicLatticeSite L => fun ν : Fin 3 => (d ν).val)
    (s := Doff L ell) (t := Fintype.piFinset (fun _ : Fin 3 => Finset.range ell))
    (fun d hd => by
      simp only [Doff, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hd
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
      exact hd)
    (fun d _ d' _ h => by
      funext ν
      exact Fin.ext (congrFun h ν))
  rw [Fintype.card_piFinset] at h
  simpa using h

theorem sub_mem_Doff {ell : ℕ} (y : PeriodicLatticeSite L)
    (u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1})
    (hu : u ∈ unitSitesOf 1 (1 * ell) y) : u.1 - y ∈ Doff L ell := by
  have hb := inBlock_of_mem_unitSites y u hu
  simp only [Doff, Finset.mem_filter, Finset.mem_univ, true_and]
  intro ν
  obtain ⟨h1, h2⟩ := hb ν
  rw [Pi.sub_apply, Fin.sub_val_of_le (Fin.le_def.mpr h1)]
  omega

theorem sum_block_le_sum_D {ell : ℕ} (y : PeriodicLatticeSite L) (F : PeriodicLatticeSite L → ℝ)
    (hF : ∀ d, 0 ≤ F d) :
    ∑ u ∈ unitSitesOf 1 (1 * ell) y, F (u.1 - y) ≤ ∑ d ∈ Doff L ell, F d := by
  classical
  have hinj : Set.InjOn (fun u : {z : PeriodicLatticeSite L // z ∈ CoarseLattice L 1} => u.1 - y)
      (unitSitesOf 1 (1 * ell) y : Set _) := fun u _ u' _ h => Subtype.ext (sub_left_inj.mp h)
  rw [← Finset.sum_image (f := F) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hF d)
  intro d hd
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
  exact sub_mem_Doff y u hu

#print axioms card_Doff_le
#print axioms sum_block_le_sum_D

end AdalyFormal.NonflatJet
