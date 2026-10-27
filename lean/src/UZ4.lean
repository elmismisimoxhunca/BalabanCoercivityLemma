import UZ3
import BLC9

/-!
# UZ4 -- from ℤ³ charts to torus `GChart`s on the ball (lane unif_20261016)

`Wof U w p ν = U (ι_w p, ν)` (the configuration in ball coordinates around `w`).
`gt_iota` : `gt (Wof U w) (g ∘ ι_w) = U^g ∘ ι_w`.
`C2 W G S t` : the clause-2 (parallel-bond difference) bound in ℤ³.
`gchart_of_C1` : a ℤ³ gauge with clause 1 at `T` on `Bz r` gives a torus gauge with `GChart` on `Ball w r` at `(T, 2T)`
(guard `2r + 1 < L + 1`).  `gchart_of_C12` : the same with a separate clause-2 bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue3 (Z3 ev iota iota_shift Box lift coord coord_iota iota_injOn)
open AdalyFormal.M2Glue2 (GChart GChart.mono frobNorm_sub_le' frobNorm_sub_comm)
open AdalyFormal.M2BallCharts (Bz Bz_sub_box ball_sub_liftL1 gchart_sub_of_zch inj_box)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

variable {L : PeriodicLatticeExtent}

/-- the configuration in ball coordinates. -/
def Wof (U : LinkCfg L) (w : PeriodicLatticeSite L) : Z3 → Fin 3 → SU2 := fun p ν => U (iota w p, ν)

theorem gt_iota (U : LinkCfg L) (w : PeriodicLatticeSite L) (g : PeriodicLatticeSite L → SU2) (p : Z3) (ν : Fin 3) :
    gt (Wof U w) (fun q => g (iota w q)) p ν = periodicGaugeTransform g U (iota w p, ν) := by
  simp only [gt, Wof, periodicGaugeTransform, iota_shift]

/-- clause 2 in ℤ³. -/
def C2 (W : Z3 → Fin 3 → SU2) (G : Z3 → SU2) (S : Set Z3) (t : ℝ) : Prop :=
  ∀ p μ ν, p ∈ S → p + ev ν ∈ S → p + ev μ ∈ S → p + ev μ + ev ν ∈ S →
    frobNorm (((gt W G (p + ev μ) ν : SU2) : M2) - ((gt W G p ν : SU2) : M2)) ≤ t

theorem C2.mono {W : Z3 → Fin 3 → SU2} {G : Z3 → SU2} {S S' : Set Z3} {t t' : ℝ} (h : C2 W G S t) (hS : S' ⊆ S)
    (ht : t ≤ t') : C2 W G S' t' :=
  fun p μ ν a b c d => (h p μ ν (hS a) (hS b) (hS c) (hS d)).trans ht

theorem C2_of_C1 {W : Z3 → Fin 3 → SU2} {G : Z3 → SU2} {S : Set Z3} {t : ℝ} (h : C1 W G S t) : C2 W G S (2 * t) := by
  intro p μ ν a b c d
  have h1 := h _ ν c (by rw [add_right_comm] at d ⊢; exact d)
  have h0 := h p ν a b
  refine (frobNorm_sub_le' _ 1 _).trans ?_
  rw [frobNorm_sub_comm (1 : M2)]
  have e : p + ev μ + ev ν = p + ev μ + ev ν := rfl
  linarith

/-- a ℤ³ gauge on `Bz r` comes from a torus gauge. -/
theorem torus_of_Z (w : PeriodicLatticeSite L) {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) (G : Z3 → SU2) :
    ∃ g : PeriodicLatticeSite L → SU2, ∀ p ∈ Box r, g (iota w p) = G p :=
  ⟨fun x => G (coord w r x), fun p hp => by simp only [coord_iota (inj_box w hL) hp]⟩

theorem gt_congr {W : Z3 → Fin 3 → SU2} {G G' : Z3 → SU2} {p : Z3} {ν : Fin 3} (h0 : G p = G' p)
    (h1 : G (p + ev ν) = G' (p + ev ν)) : gt W G p ν = gt W G' p ν := by
  simp only [gt, h0, h1]

/-- **ℤ³ chart ⇒ torus `GChart` on the ball.** -/
theorem gchart_of_C12 (U : LinkCfg L) (w : PeriodicLatticeSite L) {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1)
    {G : Z3 → SU2} {T1 T2 : ℝ} (h1 : C1 (Wof U w) G (Bz r) T1) (h2 : C2 (Wof U w) G (Bz r) T2) :
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g (Ball w r) T1 T2 := by
  obtain ⟨g, hg⟩ := torus_of_Z w hL G
  have hB : ∀ p ∈ Bz r, g (iota w p) = G p := fun p hp => hg p (Bz_sub_box hp)
  have hgt : ∀ p ν, p ∈ Bz r → p + ev ν ∈ Bz r → periodicGaugeTransform g U (iota w p, ν) = gt (Wof U w) G p ν := by
    intro p ν hp hpν
    rw [← gt_iota]; exact gt_congr (hB p hp) (hB _ hpν)
  have hz : AdalyFormal.M2Glue3.ZCh U g w (Bz r) (fun _ => T1) (fun _ => T2) := by
    refine ⟨fun p ν hp hpν => ?_, fun p μ ν a b c d => ?_⟩
    · rw [hgt p ν hp hpν]; exact h1 p ν hp hpν
    · rw [hgt _ ν c d, hgt p ν a b]; exact h2 p μ ν a b c d
  have hG := gchart_sub_of_zch (v := w) hL (S := Bz r) Bz_sub_box (P := fun _ => True) (T := Bz r) (fun p hp _ => hp) hz
  exact ⟨g, hG.mono (fun x hx => ⟨ball_sub_liftL1 w r hx, trivial⟩) le_rfl le_rfl⟩

end AdalyFormal.UnifLane.Z
