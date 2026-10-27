import R7Fork.DM7c

/-!
# DM7d -- the private (dropped) bond `d_j(b)` of a `frakB`-bond `<j,b>`: it touches `Omega_j`, it is read by its own row, by no other row of the
same level and by NO row of a lower level (`Omega_{j'+1}`-exclusion of `bondsLam j'`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_not_reads coarse_coord_add_ell_le)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.FullReparamC (pathSite_mem_block)

section private_bond
variable (P : IngrBParams)

/-- the private bond of `<j,b>`: the last fine bond of the long bond `b-hat` -/
def dB (j : ℕ) (hj : j ≤ P.k) (b : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) :
    Bond (scaleUp P.ell P.k P.Lu) := droppedBondLast (P.ell ^ j) (bhat P j hj b hb)

theorem dB_end (j : ℕ) (hj : j ≤ P.k) (b : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) :
    periodicLatticeShift (dB P j hj b hb).1 (dB P j hj b hb).2 = coarseShift b.1 (P.ell ^ j) b.2 := by
  have hn : 0 < P.ell ^ j := pow_pos P.hell j
  show periodicLatticeShift (pathSite b.1 b.2 (P.ell ^ j - 1)) b.2 = coarseShift b.1 (P.ell ^ j) b.2
  unfold pathSite coarseShift
  rw [← Function.iterate_succ_apply' (fun z => periodicLatticeShift z b.2)]
  congr 1
  omega

/-- an end-point of the private bond lies in `Om_j` -/
theorem dB_endpoint_Om {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (j : ℕ) (hj : j ≤ P.k)
    (b : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) :
    ∃ s, (s = (dB P j hj b hb).1 ∨ s = periodicLatticeShift (dB P j hj b hb).1 (dB P j hj b hb).2) ∧
      s ∈ P.S.Om j := by
  have hn : 0 < P.ell ^ j := pow_pos P.hell j
  rcases hb.1 with h | h
  · -- `b.1 ∈ Lam j`: the base of the private bond lies in the block of `b.1`
    refine ⟨(dB P j hj b hb).1, Or.inl rfl, ?_⟩
    have hfit : (b.1 b.2).val + P.ell ^ j ≤ scaleUp P.ell P.k P.Lu b.2 + 1 :=
      coarse_coord_add_ell_le (lev_dvd P j hj) b.2 _ (mem_CoarseLattice.mp (bond_coarse_site P j hj b hb) b.2)
        (b.1 b.2).isLt
    have hmem : (dB P j hj b hb).1 ∈ blockOf b.1 (P.ell ^ j) :=
      pathSite_mem_block hn b.1 b.2 (P.ell ^ j - 1) (by omega) hfit
    exact block_sub_Om P.hell hS hj (fun ρ => h.1 ρ) h.2.1 hmem
  · refine ⟨periodicLatticeShift (dB P j hj b hb).1 (dB P j hj b hb).2, Or.inr rfl, ?_⟩
    rw [dB_end P j hj b hb]
    exact (show coarseShift b.1 (P.ell ^ j) b.2 ∈ P.G.Lam j from h).2.1

/-- the private bond lies in `E_0` (touches `Omega_0`) -/
theorem dB_mem_bondsOm0 {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (j : ℕ) (hj : j ≤ P.k)
    (b : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) :
    dB P j hj b hb ∈ bondsOm0 P.G := by
  obtain ⟨s, hs, hsO⟩ := dB_endpoint_Om P hS j hj b hb
  have h0 : s ∈ P.S.Om 0 := om_anti P.S hS.1 (Nat.zero_le j) hsO
  rcases hs with rfl | rfl
  · exact Or.inl h0
  · exact Or.inr h0

/-- NO row of a LOWER level reads the private bond -/
theorem no_read_lower {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (j j' : ℕ) (hj : j ≤ P.k) (hjj : j' < j)
    (b b' : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) (hb' : b' ∈ bondsLam P.G j') :
    ¬ ReadsBond (P.ell ^ j') (bhat P j' (by omega) b' hb') (dB P j hj b hb) := by
  intro hread
  have hj' : j' ≤ P.k := by omega
  obtain ⟨s, hsd, hsO⟩ := dB_endpoint_Om P hS j hj b hb
  have hrb := reads_in_blocks (pow_pos P.hell j') (lev_dvd P j' hj') (bhat P j' hj' b' hb')
    (dB P j hj b hb) hread
  have hY : ∃ Y, (Y = b'.1 ∨ Y = coarseShift b'.1 (P.ell ^ j') b'.2) ∧ s ∈ blockOf Y (P.ell ^ j') := by
    rcases hsd with rfl | rfl
    · rcases hrb.1 with h | h
      · exact ⟨b'.1, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    · rcases hrb.2 with h | h
      · exact ⟨b'.1, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
  obtain ⟨Y, hYd, hsY⟩ := hY
  have hYc : Y ∈ CoarseLattice (scaleUp P.ell P.k P.Lu) (P.ell ^ j') := by
    rcases hYd with rfl | rfl
    · exact bond_coarse_site P j' hj' b' hb'
    · exact coarseShift_mem_coarseLattice (lev_dvd P j' hj') (bond_coarse_site P j' hj' b' hb') b'.2
  have hYdiv : ∀ ρ, P.ell ^ j' ∣ (Y ρ).val := fun ρ =>
    Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hYc) ρ)
  have hsO' : s ∈ P.S.Om (j' + 1) := om_anti P.S hS.1 (by omega : j' + 1 ≤ j) hsO
  have hYO : Y ∈ P.S.Om (j' + 1) := anchor_sub_Om P.hell hS (by omega) hYdiv hsY hsO'
  have hge := omGe_of_mem P.hell hS (by omega : j' + 1 ≤ P.k) hYO
  apply hb'.2
  rcases hYd with rfl | rfl
  · exact Or.inl hge
  · exact Or.inr hge

/-- no OTHER row of the same level reads the private bond -/
theorem no_read_same (j : ℕ) (hj : j ≤ P.k)
    (b b' : Bond (scaleUp P.ell P.k P.Lu)) (hb : b ∈ bondsLam P.G j) (hb' : b' ∈ bondsLam P.G j)
    (hne : b' ≠ b) :
    ¬ ReadsBond (P.ell ^ j) (bhat P j hj b' hb') (dB P j hj b hb) := by
  apply droppedBondLast_not_reads (pow_pos P.hell j) (lev_dvd P j hj)
  intro h
  apply hne
  have h1 := congrArg (fun c : CoarseBond (scaleUp P.ell P.k P.Lu) (P.ell ^ j) => c.1.1) h
  have h2 := congrArg (fun c : CoarseBond (scaleUp P.ell P.k P.Lu) (P.ell ^ j) => c.2) h
  exact Prod.ext h1 h2

end private_bond

#print axioms dB_endpoint_Om
#print axioms dB_mem_bondsOm0
#print axioms no_read_lower
#print axioms no_read_same

end AdalyFormal.DirichletMono
