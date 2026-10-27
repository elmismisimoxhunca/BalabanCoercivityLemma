import TL6c

/-!
# TL7a -- alignment, coarse shifts, coarse path holonomies
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)

/-- the site coordinates are multiples of `s` -/
def Aligned {L : PeriodicLatticeExtent} (s : ℕ) (x : PeriodicLatticeSite L) : Prop := ∀ μ : Fin 3, s ∣ (x μ).val

/-- the side condition on `(h, o)` making `phiS h o` respect `s`-alignment -/
structure PhiOK {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (s : ℕ) : Prop where
  side : ∀ μ, s ∣ L μ + 1
  off : ∀ μ, s ∣ o μ

theorem PhiOK.mono {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s t : ℕ} (hp : PhiOK h o s)
    (hts : t ∣ s) : PhiOK h o t := ⟨fun μ => hts.trans (hp.side μ), fun μ => hts.trans (hp.off μ)⟩

theorem aligned_phiS {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s : ℕ} (hp : PhiOK h o s)
    (x : PeriodicLatticeSite Lt) : Aligned s (phiS h o x) ↔ Aligned s x := by
  constructor
  · intro hx μ
    have h1 := hx μ
    rw [phiS_val] at h1
    have h2 : s ∣ (x μ).val + o μ := by
      have := Nat.dvd_sub_mod (n := (x μ).val + o μ) (k := L μ + 1)
      -- (x+o) = (x+o)%m + m*q
      have h3 : s ∣ ((x μ).val + o μ) % (L μ + 1) := h1
      have h4 := Nat.div_add_mod ((x μ).val + o μ) (L μ + 1)
      have h5 : s ∣ (L μ + 1) * (((x μ).val + o μ) / (L μ + 1)) := Dvd.dvd.mul_right (hp.side μ) _
      rw [← h4]; exact dvd_add h5 h3
    exact (Nat.dvd_add_left (hp.off μ)).mp h2
  · intro hx μ
    rw [phiS_val]
    have h2 : s ∣ (x μ).val + o μ := dvd_add (hx μ) (hp.off μ)
    exact Nat.dvd_mod_iff (hp.side μ) |>.mpr h2

theorem aligned_coarseShift {L : PeriodicLatticeExtent} {s : ℕ} (hs : ∀ μ, s ∣ L μ + 1) {y : PeriodicLatticeSite L}
    (hy : Aligned s y) (μ : Fin 3) : Aligned s (coarseShift y s μ) := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    rw [coarseShift_val_eq]
    exact (Nat.dvd_mod_iff (hs ν)).mpr (dvd_add (hy ν) dvd_rfl)
  · rw [coarseShift_apply_ne y s μ ν hν]; exact hy ν

theorem coarseShift_nat {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (y : PeriodicLatticeSite Lt)
    (s : ℕ) (μ : Fin 3) : phiS h o (coarseShift y s μ) = coarseShift (phiS h o y) s μ := by
  unfold coarseShift
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', phiS_shift, ih]

/-- a configuration agrees with the pull-back on edges based at `s`-aligned sites -/
def AgreeAligned {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (s : ℕ)
    (Vt : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lt)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∀ e : PeriodicLatticeEdge Lt, Aligned s e.1 → Vt e = V (phiE h o e)

theorem coarsePathHolonomy_nat {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s : ℕ} (hp : PhiOK h o s)
    {Vt : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lt}
    {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hV : AgreeAligned h o s Vt V)
    (p : List (Fin 3)) : ∀ y : PeriodicLatticeSite Lt, Aligned s y →
      coarsePathHolonomy s Vt y p = coarsePathHolonomy s V (phiS h o y) p := by
  induction p with
  | nil => intro y _; rfl
  | cons μ rest ih =>
    intro y hy
    simp only [coarsePathHolonomy]
    rw [hV (y, μ) hy, ← coarseShift_nat, ih _ (aligned_coarseShift (fun μ => (hp.side μ).trans (h μ)) hy μ)]
    rfl

end AdalyFormal.Thin
