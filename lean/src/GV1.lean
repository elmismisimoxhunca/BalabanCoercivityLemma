import GG8

/-!
# GV1 -- local integer coordinates around a site, coordinate charts (m2_glue3, 2026-10-15)

* `iota v p = v + p` (`p : ℤ³`, cast into `Fin (L μ + 1)`); `iota_shift`: forward shift = `+ e_μ`, globally.
* `Box R`, `iota_injOn`: `iota v` is injective on `Box R` when `2R < L μ + 1` (non-wrap witness).
* `coord`: a left inverse of `iota v` on `Box Rb` (classical); `lift v S = iota v '' S`.
* `bond_lift`/`sten_lift`: bonds/stencils of `lift v S` are coordinate bonds/stencils of `S` (injectivity).
* `ZCh`: chart bounds in coordinates with position-dependent constants; `gchart_lift`, `zch_of_gchart`.
* `qc`, `rho`, `Qf`: half-integer coordinates `q = p + 1/2`, `ρ = Σ|q_i|`, `Q = Σ q_i²`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open Fin.CommRing

variable {L : PeriodicLatticeExtent}

abbrev Z3 : Type := Fin 3 → ℤ

/-- unit vector. -/
def ev (μ : Fin 3) : Z3 := fun i => if i = μ then 1 else 0

/-- integer coordinates around `v`. -/
def iota (v : PeriodicLatticeSite L) (p : Z3) : PeriodicLatticeSite L :=
  fun μ => v μ + ((p μ : ℤ) : Fin (L μ + 1))

theorem iota_shift (v : PeriodicLatticeSite L) (p : Z3) (μ : Fin 3) :
    periodicLatticeShift (iota v p) μ = iota v (p + ev μ) := by
  funext ν
  simp only [periodicLatticeShift]
  rcases eq_or_ne ν μ with rfl | h
  · rw [Function.update_self]; simp only [iota, ev, Pi.add_apply, if_true]; push_cast; ring
  · rw [Function.update_of_ne h]; simp [iota, ev, h]

theorem iota_shift2 (v : PeriodicLatticeSite L) (p : Z3) (μ ν : Fin 3) :
    periodicLatticeShift (periodicLatticeShift (iota v p) μ) ν = iota v (p + ev μ + ev ν) := by
  rw [iota_shift, iota_shift]

/-! ## boxes and injectivity -/

def Box (R : ℕ) : Set Z3 := {p | ∀ i, |p i| ≤ (R : ℤ)}

theorem Box_mono {R R' : ℕ} (h : R ≤ R') : Box R ⊆ Box R' := fun p hp i =>
  (hp i).trans (by exact_mod_cast h)

theorem ev_abs (μ i : Fin 3) : |ev μ i| ≤ 1 := by
  unfold ev; split_ifs <;> norm_num

theorem add_ev_mem {R : ℕ} {p : Z3} (hp : p ∈ Box R) (μ : Fin 3) : p + ev μ ∈ Box (R + 1) := by
  intro i
  have := hp i; have := ev_abs μ i
  simp only [Pi.add_apply]; push_cast
  calc |p i + ev μ i| ≤ |p i| + |ev μ i| := abs_add_le _ _
    _ ≤ (R : ℤ) + 1 := by linarith

/-- non-wrap witness: on a torus of side `> 2R`, `iota v` is injective on `Box R`. -/
theorem iota_injOn (v : PeriodicLatticeSite L) {R : ℕ} (hL : ∀ μ, 2 * R < L μ + 1) :
    Set.InjOn (iota v) (Box R) := by
  intro p hp p' hp' h
  funext μ
  have h1 : v μ + ((p μ : ℤ) : Fin (L μ + 1)) = v μ + ((p' μ : ℤ) : Fin (L μ + 1)) := congrFun h μ
  have h2 : ((p μ : ℤ) : Fin (L μ + 1)) = ((p' μ : ℤ) : Fin (L μ + 1)) := add_left_cancel h1
  have h3 : ((p μ : ℤ) : ZMod (L μ + 1)) = ((p' μ : ℤ) : ZMod (L μ + 1)) := h2
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h3
  have hd : ((L μ + 1 : ℕ) : ℤ) ∣ (p μ - p' μ) := by
    have := dvd_sub_comm.mp h3; exact_mod_cast this
  have hb : |p μ - p' μ| < ((L μ + 1 : ℕ) : ℤ) := by
    have a := hp μ; have b := hp' μ
    have c := hL μ
    have : |p μ - p' μ| ≤ |p μ| + |p' μ| := abs_sub _ _
    have c' : (2 * (R : ℤ)) < ((L μ + 1 : ℕ) : ℤ) := by exact_mod_cast c
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hb
  linarith

/-! ## coordinates of sites -/

/-- a left inverse of `iota v` on `Box Rb`. -/
noncomputable def coord (v : PeriodicLatticeSite L) (Rb : ℕ) (x : PeriodicLatticeSite L) : Z3 :=
  open Classical in if h : ∃ p, p ∈ Box Rb ∧ iota v p = x then h.choose else 0

theorem coord_iota {v : PeriodicLatticeSite L} {Rb : ℕ} (hinj : Set.InjOn (iota v) (Box Rb)) {p : Z3}
    (hp : p ∈ Box Rb) : coord v Rb (iota v p) = p := by
  classical
  have hex : ∃ p', p' ∈ Box Rb ∧ iota v p' = iota v p := ⟨p, hp, rfl⟩
  unfold coord
  rw [dif_pos hex]
  exact hinj hex.choose_spec.1 hp hex.choose_spec.2

/-- the site set with coordinates in `S`. -/
def lift (v : PeriodicLatticeSite L) (S : Set Z3) : Set (PeriodicLatticeSite L) := iota v '' S

theorem iota_mem_lift {v : PeriodicLatticeSite L} {S : Set Z3} {p : Z3} (hp : p ∈ S) : iota v p ∈ lift v S :=
  ⟨p, hp, rfl⟩

theorem mem_lift_iff {v : PeriodicLatticeSite L} {Rb : ℕ} (hinj : Set.InjOn (iota v) (Box Rb)) {S : Set Z3}
    (hS : S ⊆ Box Rb) {p : Z3} (hp : p ∈ Box Rb) : iota v p ∈ lift v S ↔ p ∈ S := by
  constructor
  · rintro ⟨p', hp', he⟩
    have := hinj (hS hp') hp he
    rw [← this]; exact hp'
  · exact iota_mem_lift

theorem bond_lift {v : PeriodicLatticeSite L} {Rb : ℕ} (hinj : Set.InjOn (iota v) (Box (Rb + 1))) {S : Set Z3}
    (hS : S ⊆ Box Rb) {x : PeriodicLatticeSite L} {ν : Fin 3} (hx : x ∈ lift v S)
    (hxν : periodicLatticeShift x ν ∈ lift v S) : ∃ p, x = iota v p ∧ p ∈ S ∧ p + ev ν ∈ S := by
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨p, rfl, hp, ?_⟩
  rw [iota_shift] at hxν
  have hb : p + ev ν ∈ Box (Rb + 1) := add_ev_mem (hS hp) ν
  obtain ⟨p', hp', he⟩ := hxν
  have := hinj (Box_mono (Nat.le_succ Rb) (hS hp')) hb he
  rw [← this]; exact hp'

theorem sten_lift {v : PeriodicLatticeSite L} {Rb : ℕ} (hinj : Set.InjOn (iota v) (Box (Rb + 1))) {S : Set Z3}
    (hS : S ⊆ Box Rb) {x : PeriodicLatticeSite L} {μ ν : Fin 3} (h0 : x ∈ lift v S)
    (h1 : periodicLatticeShift x ν ∈ lift v S) (h2 : periodicLatticeShift x μ ∈ lift v S)
    (h3 : periodicLatticeShift (periodicLatticeShift x μ) ν ∈ lift v S) :
    ∃ p, x = iota v p ∧ p ∈ S ∧ p + ev ν ∈ S ∧ p + ev μ ∈ S ∧ p + ev μ + ev ν ∈ S := by
  have B : ∀ {a b : Z3}, a ∈ S → b ∈ S → iota v a = iota v b → a = b := fun ha hb e =>
    hinj (Box_mono (Nat.le_succ Rb) (hS ha)) (Box_mono (Nat.le_succ Rb) (hS hb)) e
  obtain ⟨p, rfl, hp, hpν⟩ := bond_lift hinj hS h0 h1
  obtain ⟨p', e', hp', hpμ⟩ := bond_lift hinj hS h0 h2
  have := B hp hp' e'; subst this
  obtain ⟨p'', e'', hp'', hpμν⟩ := bond_lift hinj hS h2 h3
  rw [iota_shift] at e''
  have := B hpμ hp'' e''; subst this
  exact ⟨p, rfl, hp, hpν, hpμ, hpμν⟩

/-! ## coordinate charts with local constants -/

/-- chart bounds in coordinates, with position-dependent constants. -/
def ZCh (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (v : PeriodicLatticeSite L) (S : Set Z3)
    (T1 T2 : Z3 → ℝ) : Prop :=
  (∀ p ν, p ∈ S → p + ev ν ∈ S →
      frobNorm (((periodicGaugeTransform g U (iota v p, ν) : SU2) : M2) - 1) ≤ T1 p) ∧
  (∀ p μ ν, p ∈ S → p + ev ν ∈ S → p + ev μ ∈ S → p + ev μ + ev ν ∈ S →
      frobNorm (((periodicGaugeTransform g U (iota v (p + ev μ), ν) : SU2) : M2)
        - (periodicGaugeTransform g U (iota v p, ν) : SU2)) ≤ T2 p)

theorem ZCh.mono {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {v : PeriodicLatticeSite L} {S S' : Set Z3}
    {T1 T2 T1' T2' : Z3 → ℝ} (h : ZCh U g v S T1 T2) (hS : S' ⊆ S) (h1 : ∀ p ∈ S', T1 p ≤ T1' p)
    (h2 : ∀ p ∈ S', T2 p ≤ T2' p) : ZCh U g v S' T1' T2' :=
  ⟨fun p ν a b => (h.1 p ν (hS a) (hS b)).trans (h1 p a),
   fun p μ ν a b c d => (h.2 p μ ν (hS a) (hS b) (hS c) (hS d)).trans (h2 p a)⟩

theorem gchart_lift {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {v : PeriodicLatticeSite L} {Rb : ℕ}
    (hinj : Set.InjOn (iota v) (Box (Rb + 1))) {S : Set Z3} (hS : S ⊆ Box Rb) {T1 T2 : Z3 → ℝ}
    (h : ZCh U g v S T1 T2) {a b : ℝ} (hb : ∀ p ∈ S, T1 p ≤ a ∧ T2 p ≤ b) :
    GChart U g (lift v S) a b := by
  refine ⟨fun x ν hx hxν => ?_, fun x μ ν h0 h1 h2 h3 => ?_⟩
  · obtain ⟨p, rfl, hp, hpν⟩ := bond_lift hinj hS hx hxν
    exact (h.1 p ν hp hpν).trans (hb p hp).1
  · obtain ⟨p, rfl, hp, hpν, hpμ, hpμν⟩ := sten_lift hinj hS h0 h1 h2 h3
    rw [iota_shift]
    exact (h.2 p μ ν hp hpν hpμ hpμν).trans (hb p hp).2

theorem zch_of_gchart {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {v : PeriodicLatticeSite L}
    {S : Set Z3} {a b : ℝ} (h : GChart U g (lift v S) a b) : ZCh U g v S (fun _ => a) (fun _ => b) := by
  refine ⟨fun p ν hp hpν => ?_, fun p μ ν h0 h1 h2 h3 => ?_⟩
  · have := h.1 (iota v p) ν (iota_mem_lift hp) (by rw [iota_shift]; exact iota_mem_lift hpν)
    exact this
  · have := h.2 (iota v p) μ ν (iota_mem_lift h0) (by rw [iota_shift]; exact iota_mem_lift h1)
      (by rw [iota_shift]; exact iota_mem_lift h2) (by rw [iota_shift2]; exact iota_mem_lift h3)
    rw [iota_shift] at this
    exact this

/-! ## half-integer coordinates -/

noncomputable def qc (p : Z3) (i : Fin 3) : ℝ := (p i : ℝ) + 1 / 2

noncomputable def rho (p : Z3) : ℝ := |qc p 0| + |qc p 1| + |qc p 2|

noncomputable def Qf (p : Z3) : ℝ := qc p 0 ^ 2 + qc p 1 ^ 2 + qc p 2 ^ 2

theorem half_le_abs_qc (p : Z3) (i : Fin 3) : 1 / 2 ≤ |qc p i| := by
  unfold qc
  rcases le_or_gt 0 (p i) with h | h
  · have : (0 : ℝ) ≤ (p i : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (p i : ℝ) ≤ -1 := by exact_mod_cast (show p i ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]; linarith

theorem rho_ge (p : Z3) : 3 / 2 ≤ rho p := by
  unfold rho
  linarith [half_le_abs_qc p 0, half_le_abs_qc p 1, half_le_abs_qc p 2]

theorem rho_pos (p : Z3) : 0 < rho p := by linarith [rho_ge p]

theorem qc_add_ev (p : Z3) (μ i : Fin 3) : qc (p + ev μ) i = qc p i + (if i = μ then 1 else 0) := by
  unfold qc ev; simp only [Pi.add_apply]; split_ifs <;> push_cast <;> ring

theorem abs_qc_add_ev_le (p : Z3) (μ i : Fin 3) : |qc (p + ev μ) i - qc p i| ≤ 1 := by
  rw [qc_add_ev]; split_ifs <;> norm_num

theorem rho_le_three_mul (p : Z3) : ∀ i, |qc p i| ≤ rho p := by
  intro i; unfold rho
  have := abs_nonneg (qc p 0); have := abs_nonneg (qc p 1); have := abs_nonneg (qc p 2)
  fin_cases i <;> simp <;> linarith

/-- `ρ` is 1-Lipschitz along coordinate perturbations. -/
theorem rho_perturb {p p' : Z3} {k : ℝ} (h : ∀ i, |qc p' i - qc p i| ≤ k) :
    rho p' ≤ rho p + 3 * k ∧ rho p - 3 * k ≤ rho p' := by
  unfold rho
  have a := h 0; have b := h 1; have c := h 2
  have e : ∀ i, |qc p' i| ≤ |qc p i| + k ∧ |qc p i| ≤ |qc p' i| + k := by
    intro i
    have := h i
    constructor
    · calc |qc p' i| = |qc p i + (qc p' i - qc p i)| := by ring_nf
        _ ≤ |qc p i| + |qc p' i - qc p i| := abs_add_le _ _
        _ ≤ |qc p i| + k := by linarith
    · calc |qc p i| = |qc p' i - (qc p' i - qc p i)| := by ring_nf
        _ ≤ |qc p' i| + |qc p' i - qc p i| := abs_sub _ _
        _ ≤ |qc p' i| + k := by linarith
  have e0 := e 0; have e1 := e 1; have e2 := e 2
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2]

theorem Qf_ge (p : Z3) : rho p ^ 2 ≤ 3 * Qf p := by
  unfold rho Qf
  have h0 := sq_abs (qc p 0); have h1 := sq_abs (qc p 1); have h2 := sq_abs (qc p 2)
  nlinarith [sq_nonneg (|qc p 0| - |qc p 1|), sq_nonneg (|qc p 1| - |qc p 2|), sq_nonneg (|qc p 0| - |qc p 2|)]

theorem Qf_le (p : Z3) : Qf p ≤ rho p ^ 2 := by
  unfold rho Qf
  have h0 := sq_abs (qc p 0); have h1 := sq_abs (qc p 1); have h2 := sq_abs (qc p 2)
  have := abs_nonneg (qc p 0); have := abs_nonneg (qc p 1); have := abs_nonneg (qc p 2)
  nlinarith [mul_nonneg (abs_nonneg (qc p 0)) (abs_nonneg (qc p 1)),
    mul_nonneg (abs_nonneg (qc p 1)) (abs_nonneg (qc p 2)), mul_nonneg (abs_nonneg (qc p 0)) (abs_nonneg (qc p 2))]

theorem Qf_pos (p : Z3) : 0 < Qf p := by
  have := Qf_ge p; have := rho_ge p; nlinarith

theorem Qf_add_ev (p : Z3) (μ : Fin 3) : Qf (p + ev μ) = Qf p + 2 * qc p μ + 1 := by
  unfold Qf
  simp only [qc_add_ev]
  fin_cases μ <;> simp <;> ring

end AdalyFormal.M2Glue3
