import NV4
import ZR6A

/-!
# NV5 -- `CoversOm0p ell M 12 2 (slab3 ..)`: every site and every plaquette of `Ω₀` lies in one class cube (lane nonvac_20261015)

Generalises `StatementLaneG.TT2_coversp` (ell = 2, M = 2, k = 1, N = 120) to symbolic parameters.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVac

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem shift_val_N {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (s : PeriodicLatticeSite L) (μ ρ : Fin 3) :
    ((periodicLatticeShift s μ) ρ).val = if ρ = μ then ((s ρ).val + 1) % N else (s ρ).val := by
  unfold periodicLatticeShift
  by_cases h : ρ = μ
  · subst h
    simp only [Function.update_self, if_true]
    rw [Fin.val_add, Fin.val_one']
    have h1 := hN ρ
    have h2 : 1 % (L ρ + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h2]
    generalize ((s ρ).val) = v
    rw [h1]
  · simp [Function.update_of_ne h, h]

theorem adj_shift_N {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    {x s : PeriodicLatticeSite L} (h : Adj N x s) (μ : Fin 3) (hμ : (s μ).val = (x μ).val) :
    Adj N x (periodicLatticeShift s μ) := by
  intro ρ
  rw [shift_val_N hN hN1]
  by_cases hρ : ρ = μ
  · subst hρ; simp only [if_true]; right; rw [hμ]
  · simp only [if_neg hρ]; exact h ρ

theorem adj_shift_coord_N {L : PeriodicLatticeExtent} {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (s : PeriodicLatticeSite L) {μ ν : Fin 3} (hne : ν ≠ μ) :
    ((periodicLatticeShift s μ) ν).val = (s ν).val := by
  rw [shift_val_N hN hN1, if_neg hne]

section
variable {M ell R N P0 Q0 P1 Q1 P2 Q2 : ℕ}

theorem slab3_coversp (G : SlabGeo M ell R N P0 Q0 P1 Q1 P2 Q2)
    (w0L : P0 + 12 * M ≤ P2) (w0R : Q2 + 12 * M ≤ Q0) (w1 : P1 + 12 * (M * ell) ≤ Q1)
    (w2 : P2 + 12 * (M * ell ^ 2) ≤ Q2) (hQN : Q0 < N) (hP12 : P1 < P2) (hQ21 : Q2 < Q1) (hQ10 : Q1 < Q0)
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = N) :
    CoversOm0p ell M 12 2 (slab3 L P0 Q0 P1 Q1 P2 Q2) := by
  have hN1 : 1 < N := by
    have := G.nest21; have := G.nest10; have := G.nestw; omega
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [om0_mem] at hx
    obtain ⟨sites, j, hc, hall⟩ := cube_nbhd G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN x hx
    exact ⟨sites, j, hc, hall x (adj_refl N x) hx.1 hx.2⟩
  · intro p hp
    have hmu : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have hnu : p.2.1.2 ≠ p.2.1.1 := fun h => hmu h.symm
    have hmem : ∀ e : PeriodicLatticeEdge L, e ∈ periodicPlaquetteBoundaryEdges p ↔
        (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
          e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
      intro e
      simp [periodicPlaquetteBoundaryEdges]
    have hx : P0 ≤ (p.1 0).val ∧ (p.1 0).val < Q0 := by
      have := (hp (p.1, p.2.1.1) ((hmem _).mpr (Or.inl rfl))).1
      rwa [om0_mem] at this
    obtain ⟨sites, j, hc, hall⟩ := cube_nbhd G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN p.1 hx
    refine ⟨sites, j, hc, fun e he => ?_⟩
    have hcb := hp e he
    obtain ⟨hcb1, hcb2⟩ := hcb
    rw [om0_mem] at hcb1 hcb2
    have a0 : Adj N p.1 p.1 := adj_refl N _
    have aμ : Adj N p.1 (periodicLatticeShift p.1 p.2.1.1) := adj_shift_N hN hN1 a0 _ rfl
    have aν : Adj N p.1 (periodicLatticeShift p.1 p.2.1.2) := adj_shift_N hN hN1 a0 _ rfl
    have aμν : Adj N p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2) :=
      adj_shift_N hN hN1 aμ _ (adj_shift_coord_N hN hN1 _ hnu)
    have aνμ : Adj N p.1 (periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1) :=
      adj_shift_N hN hN1 aν _ (adj_shift_coord_N hN hN1 _ hmu)
    refine ⟨?_, ?_⟩
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ a0 hcb1.1 hcb1.2
      · exact hall _ aμ hcb1.1 hcb1.2
      · exact hall _ aν hcb1.1 hcb1.2
      · exact hall _ a0 hcb1.1 hcb1.2
    · rcases (hmem e).mp he with rfl | rfl | rfl | rfl
      · exact hall _ aμ hcb2.1 hcb2.2
      · exact hall _ aμν hcb2.1 hcb2.2
      · exact hall _ aνμ hcb2.1 hcb2.2
      · exact hall _ aν hcb2.1 hcb2.2

end

end AdalyFormal.NonVac
