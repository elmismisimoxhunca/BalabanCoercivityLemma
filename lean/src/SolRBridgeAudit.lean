import RB4
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace SolRBridge
open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.RBridge

-- A coarser/larger base law is NOT refuted by the fine zero-level collar.
theorem readingB_satisfies_collar {L : PeriodicLatticeExtent} {ell M R k : ℕ}
    (hell : 0 < ell) (hM : 0 < M) (Om1 : Set (PeriodicLatticeSite L)) :
    Collar0 M R (Om0Unit ell M R k Om1) Om1 := by
  intro x hx y hy
  apply om0Print_collar Om1 x _ y hy
  exact fun h => hx (om0Print_sub_unit hell hM Om1 h)

theorem readingB_fine_blockClosed {L : PeriodicLatticeExtent} (ell M R k : ℕ)
    (Om1 : Set (PeriodicLatticeSite L)) : BlockClosed M (Om0Unit ell M R k Om1) := by
  intro x hx x' hs
  apply om0Rad_blockClosed (M * ell ^ k) (R * (M * ell ^ k)) Om1 x hx x'
  intro μ
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hs μ]

def x400 : PeriodicLatticeSite Lw := fun μ => if μ = 0 then 4 else 0

theorem readingB_strictly_larger :
    x400 ∈ Om0Unit 2 2 1 1 Om1w ∧ x400 ∉ Om0Print 2 1 Om1w := by
  constructor
  · refine ⟨BigBlockCell 4 (fun μ => (x400 μ).val / 4), ⟨_, rfl⟩,
      ⟨x400, fun _ => rfl, zeroSite, rfl, ?_⟩, fun _ => rfl⟩
    unfold pdist pcd x400 zeroSite Lw
    decide
  · rintro ⟨A, ⟨b, rfl⟩, ⟨z, hz, y, hy, hd⟩, hx⟩
    have hy' : y = zeroSite := hy
    subst hy'
    have hz0 : ∀ μ, (z μ).val / 2 = (x400 μ).val / 2 := fun μ => by rw [hz μ, ← hx μ]
    have c0 := hz0 0; have c1 := hz0 1; have c2 := hz0 2
    simp [x400, Lw] at c0 c1 c2
    have e0 := (z 0).isLt; have e1 := (z 1).isLt; have e2 := (z 2).isLt
    simp [Lw] at e0 e1 e2
    unfold pdist pcd zeroSite Lw at hd
    simp only [Fin.sum_univ_three, Fin.val_zero] at hd
    split_ifs at hd <;> omega

-- S83: the actual imported bond predicate uses BOTH endpoints, while CMP96 p.224 uses OR.
def Incident {L : PeriodicLatticeExtent} (Ω : Set (PeriodicLatticeSite L))
    (b : AdalyFormal.Balaban.AdmissibleSubspace.Bond L) : Prop :=
  b.1 ∈ Ω ∨ periodicLatticeShift b.1 b.2 ∈ Ω

def boundaryBond : AdalyFormal.Balaban.AdmissibleSubspace.Bond Lw := (zeroSite, 0)

theorem boundary_bond_omitted : Incident Om1w boundaryBond ∧ ¬ CubeBond Om1w boundaryBond := by
  constructor
  · exact Or.inl rfl
  · intro h
    have hzero : periodicLatticeShift zeroSite 0 = zeroSite := h.2
    have hv := congrArg (fun z : PeriodicLatticeSite Lw => (z 0).val) hzero
    norm_num [periodicLatticeShift, zeroSite, Lw] at hv

-- A and B are not distinguished by the zero collar alone; minimality is extra information.
end SolRBridge
#print axioms SolRBridge.readingB_satisfies_collar
#print axioms SolRBridge.readingB_fine_blockClosed
#print axioms SolRBridge.readingB_strictly_larger
#print axioms SolRBridge.boundary_bond_omitted
