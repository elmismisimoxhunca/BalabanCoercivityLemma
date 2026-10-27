import UW4

/-!
# UW5 -- the clause-2 stacking step, part 1: the frozen gauge `G0` and the velocity field `V` (lane unif_20261016)

Geometry: a slab `SlabS σ lo hi a b = {p | transverse coordinates in [lo, hi], a ≤ p σ < b}`; old part `O = SlabS c0 c`,
new part `N = SlabS c ch`, `c0 + 2 ≤ c < ch`.  Data: charts `Go` on `O`, `Gn` on `N` (clauses 1, 2), holonomy bound `η`.
`bp p` = the projection to the plane `p σ = c`.
* `Tz x = Go(x−σ) W(x−σ,σ) Gn(x)⁻¹`, `Az x = U^{Go}(x−2σ, σ)` (the bond two layers below), `kap0 = Az⁻¹ Tz`,
  `G0 p = kap0 (bp p) · Gn p`, `Vf x = icay (Az⁻¹ · U^{G0}(x, σ))`.
* `g0_plane` : the plaquette identity `U^{G0}(x,ν) = Az(x)⁻¹ · (Go(x−σ) hol⁻¹ Go(x−σ)⁻¹) · U^{Go}(x−σ,ν) · Az(x+ν)` on the plane.
* `kap0_d1` : `|kap0(x+ν) − kap0 x| ≤ K0`, `K0 = 3 o1 + η + n1`.
* `g0_c1`, `g0_c2` : `G0` is a chart on `N` with constants `g01 = n1 + K0`, `g02 = 3 o2 + 2η + 3 n2 + 4 n1 K0`.
* `vf_bound`, `vf_d1` : `|Vf| ≤ VB = o1 + n1`, plane differences `≤ Dv = 2 (o2 + n2 + 2 n1 K0)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open Matrix
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (frobNorm_sub_le' frobNorm_sub_comm frobNorm_su2_mul frobNorm_mul_su2 gauge_step_one frobNorm_add3_le frobNorm_mul_le frobNorm_mul_su2_star
  gauge_step_two icay cay acos2 acos2_nonneg cay_icay frobNorm_icay_sub_le frobNorm_icay_le isSu2_icay)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul IsSu2)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

/-- transverse box constraint. -/
def TrB (σ : Fin 3) (lo hi : Z3) (p : Z3) : Prop := ∀ ν, ν ≠ σ → lo ν ≤ p ν ∧ p ν ≤ hi ν

/-- the slab. -/
def SlabS (σ : Fin 3) (lo hi : Z3) (a b : ℤ) : Set Z3 := {p | TrB σ lo hi p ∧ a ≤ p σ ∧ p σ < b}

/-- projection to the plane. -/
def bp (σ : Fin 3) (c : ℤ) (p : Z3) : Z3 := setc p σ c

def Tz (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (Go Gn : Z3 → SU2) (x : Z3) : SU2 :=
  Go (x - ev σ) * W (x - ev σ) σ * (Gn x)⁻¹

def Az (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (Go : Z3 → SU2) (x : Z3) : SU2 := gt W Go (x - ev σ - ev σ) σ

def kap0 (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (Go Gn : Z3 → SU2) (x : Z3) : SU2 :=
  (Az W σ Go x)⁻¹ * Tz W σ Go Gn x

def G0 (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (c : ℤ) (Go Gn : Z3 → SU2) (p : Z3) : SU2 :=
  kap0 W σ Go Gn (bp σ c p) * Gn p

noncomputable def Vf (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (c : ℤ) (Go Gn : Z3 → SU2) (x : Z3) : M2 :=
  icay ((Az W σ Go x)⁻¹ * gt W (G0 W σ c Go Gn) x σ)

theorem bp_add_self (σ : Fin 3) (c : ℤ) (p : Z3) : bp σ c (p + ev σ) = bp σ c p := setc_add_self p σ c
theorem bp_add_ne (σ : Fin 3) (c : ℤ) (p : Z3) {ν : Fin 3} (h : ν ≠ σ) : bp σ c (p + ev ν) = bp σ c p + ev ν :=
  setc_add_ne p c h
theorem bp_of_plane (σ : Fin 3) {c : ℤ} {p : Z3} (h : p σ = c) : bp σ c p = p := by
  unfold bp; rw [← h, setc_eq_self]

/-- `G0` on the plane: `G0 x = Az(x)⁻¹ Go(x−σ) W(x−σ,σ)`. -/
theorem g0_plane_val (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (c : ℤ) (Go Gn : Z3 → SU2) {x : Z3} (hxc : x σ = c) :
    G0 W σ c Go Gn x = (Az W σ Go x)⁻¹ * Go (x - ev σ) * W (x - ev σ) σ := by
  simp only [G0, bp_of_plane σ hxc, kap0, Tz]; group

/-- **the plaquette identity on the plane.** -/
theorem g0_plane (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (c : ℤ) (Go Gn : Z3 → SU2) {x : Z3} (hxc : x σ = c) {ν : Fin 3} (hν : ν ≠ σ) :
    gt W (G0 W σ c Go Gn) x ν
      = (Az W σ Go x)⁻¹ * (Go (x - ev σ) * (hol W (x - ev σ) ν σ)⁻¹ * (Go (x - ev σ))⁻¹)
        * gt W Go (x - ev σ) ν * Az W σ Go (x + ev ν) := by
  have hxc' : (x + ev ν) σ = c := by simp [ev_apply_ne (Ne.symm hν), hxc]
  simp only [gt]
  rw [g0_plane_val W σ c Go Gn hxc, g0_plane_val W σ c Go Gn hxc']
  have e1 : x + ev ν - ev σ = x - ev σ + ev ν := by abel
  have e2 : x - ev σ + ev σ = x := by abel
  rw [e1]
  simp only [hol, e2]
  group


section frozen
variable (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (lo hi : Z3) (c0 c ch : ℤ) (Go Gn : Z3 → SU2)
  (hc0 : c0 + 2 ≤ c) (hch : c < ch)
include hc0 hch

theorem bp_mem {p : Z3} (hp : p ∈ SlabS σ lo hi c ch) : bp σ c p ∈ SlabS σ lo hi c ch := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨fun ν hν => ?_, ?_, ?_⟩
  · simp only [bp, setc_ne _ _ hν]; exact h1 ν hν
  · simp [bp, setc_self]
  · simp [bp, setc_self]; exact hch

theorem plane_below {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) :
    x - ev σ ∈ SlabS σ lo hi c0 c ∧ x - ev σ - ev σ ∈ SlabS σ lo hi c0 c := by
  obtain ⟨h1, _, _⟩ := hx
  have hs : ∀ (k : ℤ) (q : Z3), (∀ ν, ν ≠ σ → q ν = x ν) → q σ = c - k → 1 ≤ k → k ≤ 2 → q ∈ SlabS σ lo hi c0 c := by
    intro k q hq hqs hk1 hk2
    exact ⟨fun ν hν => by rw [hq ν hν]; exact h1 ν hν, by omega, by omega⟩
  refine ⟨hs 1 _ (fun ν hν => ?_) ?_ le_rfl (by norm_num), hs 2 _ (fun ν hν => ?_) ?_ (by norm_num) le_rfl⟩
  · simp [ev_apply_ne hν]
  · simp [ev_apply_self, hxc]
  · simp [ev_apply_ne hν]
  · simp [ev_apply_self, hxc]; ring

end frozen

theorem slab_mono {σ : Fin 3} {lo hi : Z3} {a b a' b' : ℤ} (h1 : a' ≤ a) (h2 : b ≤ b') {p : Z3} (hp : p ∈ SlabS σ lo hi a b) :
    p ∈ SlabS σ lo hi a' b' := ⟨hp.1, by have := hp.2.1; omega, by have := hp.2.2; omega⟩

theorem tr_add_ne {σ : Fin 3} {lo hi : Z3} {p : Z3} {ν : Fin 3} (hν : ν = σ) (hp : TrB σ lo hi p) : TrB σ lo hi (p + ev ν) := by
  intro κ hκ; subst hν; simp only [Pi.add_apply, ev_apply_ne hκ, add_zero]; exact hp κ hκ

theorem plane_N {σ : Fin 3} {lo hi : Z3} {c ch : ℤ} (hch : c + 2 ≤ ch) {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) : x + ev σ ∈ SlabS σ lo hi c ch :=
  ⟨tr_add_ne rfl hx.1, by simp [ev_apply_self]; omega, by simp [ev_apply_self]; omega⟩

/-- the `κ₀` jump bound. -/
noncomputable def K0c (o1 n1 η : ℝ) : ℝ := 3 * o1 + η + n1

theorem bp_plane (σ : Fin 3) (c : ℤ) (p : Z3) : (bp σ c p) σ = c := setc_self p σ c

theorem gt_G0 (W : Z3 → Fin 3 → SU2) (σ : Fin 3) (c : ℤ) (Go Gn : Z3 → SU2) (p : Z3) (ν : Fin 3) :
    gt W (G0 W σ c Go Gn) p ν
      = kap0 W σ Go Gn (bp σ c p) * gt W Gn p ν * (kap0 W σ Go Gn (bp σ c (p + ev ν)))⁻¹ :=
  gt_mul W (fun q => kap0 W σ Go Gn (bp σ c q)) Gn p ν

noncomputable def g01c (o1 n1 η : ℝ) : ℝ := n1 + K0c o1 n1 η
noncomputable def g02c (o1 o2 n1 n2 η : ℝ) : ℝ := 3 * o2 + 2 * η + 3 * n2 + 4 * n1 * K0c o1 n1 η

theorem frobNorm_zero' : frobNorm (0 : M2) = 0 := by
  have := frobNorm_smul (0 : ℝ) (0 : M2); simpa using this

theorem bracket_bound (K0 K1 K2 K3 : SU2) (D0 D2 : M2) :
    frobNorm ((K2 : M2) * D2 * (K3 : M2)ᴴ - (K0 : M2) * D0 * (K1 : M2)ᴴ)
      ≤ frobNorm ((K2 : M2) - (K0 : M2)) * frobNorm D2 + frobNorm (D2 - D0)
        + frobNorm D0 * frobNorm ((K3 : M2) - (K1 : M2)) := by
  have e : (K2 : M2) * D2 * (K3 : M2)ᴴ - (K0 : M2) * D0 * (K1 : M2)ᴴ
      = ((K2 : M2) - (K0 : M2)) * D2 * (K3 : M2)ᴴ + (K0 : M2) * (D2 - D0) * (K3 : M2)ᴴ + (K0 : M2) * (D0 * ((K3 : M2) - (K1 : M2))ᴴ) := by
    simp only [conjTranspose_sub]; noncomm_ring
  rw [e]
  refine (frobNorm_add3_le _ _ _).trans ?_
  have a : frobNorm (((K2 : M2) - (K0 : M2)) * D2 * (K3 : M2)ᴴ) ≤ frobNorm ((K2 : M2) - (K0 : M2)) * frobNorm D2 := by
    rw [frobNorm_mul_su2_star]; exact frobNorm_mul_le _ _
  have b : frobNorm ((K0 : M2) * (D2 - D0) * (K3 : M2)ᴴ) = frobNorm (D2 - D0) := by
    rw [frobNorm_mul_su2_star, frobNorm_su2_mul]
  have c : frobNorm ((K0 : M2) * (D0 * ((K3 : M2) - (K1 : M2))ᴴ)) ≤ frobNorm D0 * frobNorm ((K3 : M2) - (K1 : M2)) := by
    rw [frobNorm_su2_mul]; have := frobNorm_mul_le D0 ((K3 : M2) - (K1 : M2))ᴴ
    rwa [AdalyFormal.M2Glue2.frobNorm_conjTranspose] at this
  linarith

theorem gt_coe (W : Z3 → Fin 3 → SU2) (κ G : Z3 → SU2) (p : Z3) (ν : Fin 3) :
    ((κ p * gt W G p ν * (κ (p + ev ν))⁻¹ : SU2) : M2) = (κ p : M2) * (gt W G p ν : M2) * (κ (p + ev ν) : M2)ᴴ := by
  rw [coe_mul, coe_mul, coe_inv]

section bounds
variable {W : Z3 → Fin 3 → SU2} {σ : Fin 3} {lo hi : Z3} {c0 c ch : ℤ} {Go Gn : Z3 → SU2}
  (hc0 : c0 + 2 ≤ c) (hch : c + 2 ≤ ch)
  {o1 o2 n1 n2 η : ℝ}
  (hO1 : C1 W Go (SlabS σ lo hi c0 c) o1) (hO2 : C2 W Go (SlabS σ lo hi c0 c) o2)
  (hN1 : C1 W Gn (SlabS σ lo hi c ch) n1) (hN2 : C2 W Gn (SlabS σ lo hi c ch) n2)
  (hH : HolB W (SlabS σ lo hi c0 ch) η)
include hc0 hch

include hO1 in
theorem az_bound {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) :
    frobNorm (((Az W σ Go x : SU2) : M2) - 1) ≤ o1 := by
  have hb := plane_below σ lo hi c0 c ch hc0 (by omega) hx hxc
  have := hO1 (x - ev σ - ev σ) σ hb.2 (by rw [show x - ev σ - ev σ + ev σ = x - ev σ by abel]; exact hb.1)
  exact this

include hO1 hH in
theorem g0_plane_bond {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) {ν : Fin 3} (hν : ν ≠ σ)
    (hxν : x + ev ν ∈ SlabS σ lo hi c ch) :
    frobNorm (((gt W (G0 W σ c Go Gn) x ν : SU2) : M2) - 1) ≤ 3 * o1 + η := by
  have hxc' : (x + ev ν) σ = c := by simp [ev_apply_ne (Ne.symm hν), hxc]
  rw [g0_plane W σ c Go Gn hxc hν]
  refine (prod4_sub_one _ _ _ _).trans ?_
  have hb := plane_below σ lo hi c0 c ch hc0 (by omega) hx hxc
  have hb' := plane_below σ lo hi c0 c ch hc0 (by omega) hxν hxc'
  have a1 : frobNorm ((((Az W σ Go x)⁻¹ : SU2) : M2) - 1) ≤ o1 := by
    rw [n_inv]; exact az_bound hc0 hch hO1 hx hxc
  have a2 : frobNorm (((Go (x - ev σ) * (hol W (x - ev σ) ν σ)⁻¹ * (Go (x - ev σ))⁻¹ : SU2) : M2) - 1) ≤ η := by
    rw [n_conj, n_inv]
    have hq : x - ev σ ∈ SlabS σ lo hi c0 ch := slab_mono (le_refl _) (by omega) hb.1
    have hqν : x - ev σ + ev ν ∈ SlabS σ lo hi c0 ch := by
      rw [show x - ev σ + ev ν = x + ev ν - ev σ by abel]; exact slab_mono (le_refl _) (by omega) hb'.1
    have hqσ : x - ev σ + ev σ ∈ SlabS σ lo hi c0 ch := by
      rw [show x - ev σ + ev σ = x by abel]; exact slab_mono (by omega) (le_refl _) hx
    have hqνσ : x - ev σ + ev ν + ev σ ∈ SlabS σ lo hi c0 ch := by
      rw [show x - ev σ + ev ν + ev σ = x + ev ν by abel]; exact slab_mono (by omega) (le_refl _) hxν
    exact hH _ ν σ hq hqν hqσ hqνσ
  have a3 : frobNorm (((gt W Go (x - ev σ) ν : SU2) : M2) - 1) ≤ o1 :=
    hO1 _ ν hb.1 (by rw [show x - ev σ + ev ν = x + ev ν - ev σ by abel]; exact hb'.1)
  have a4 := az_bound hc0 hch hO1 hxν hxc'
  linarith

include hO1 hH hN1 in
theorem kap0_d1 {x : Z3} (hx : x ∈ SlabS σ lo hi c ch) (hxc : x σ = c) {ν : Fin 3} (hν : ν ≠ σ)
    (hxν : x + ev ν ∈ SlabS σ lo hi c ch) :
    frobNorm (((kap0 W σ Go Gn (x + ev ν) : SU2) : M2) - kap0 W σ Go Gn x) ≤ K0c o1 n1 η := by
  have hxc' : (x + ev ν) σ = c := by simp [ev_apply_ne (Ne.symm hν), hxc]
  have e : gt W (G0 W σ c Go Gn) x ν = kap0 W σ Go Gn x * gt W Gn x ν * (kap0 W σ Go Gn (x + ev ν))⁻¹ := by
    have := gt_mul W (fun q => kap0 W σ Go Gn (bp σ c q)) Gn x ν
    simp only [bp_of_plane σ hxc, bp_of_plane σ hxc'] at this
    exact this
  have h := su2_sub_rel e
  have a := g0_plane_bond (Gn := Gn) hc0 hch hO1 hH hx hxc hν hxν
  have b := hN1 x ν hx hxν
  unfold K0c; linarith

include hO1 hH hN1 in
/-- `G0` is a clause-1 chart on `N`. -/
theorem g0_c1 (ho1 : 0 ≤ o1) (hn1 : 0 ≤ n1) (hη : 0 ≤ η) :
    C1 W (G0 W σ c Go Gn) (SlabS σ lo hi c ch) (g01c o1 n1 η) := by
  intro p ν hp hpν
  rw [gt_G0]
  by_cases hν : ν = σ
  · subst hν
    rw [bp_add_self, n_conj]
    have := hN1 p ν hp hpν
    unfold g01c K0c; linarith
  · refine (gauge_step_one _ _ _).trans ?_
    rw [bp_add_ne σ c p hν]
    have hb := bp_mem σ lo hi c0 c ch hc0 (by omega) hp
    have hbν : bp σ c p + ev ν ∈ SlabS σ lo hi c ch := by rw [← bp_add_ne σ c p hν]; exact bp_mem σ lo hi c0 c ch hc0 (by omega) hpν
    have k := kap0_d1 hc0 hch hO1 hN1 hH hb (bp_plane σ c p) hν hbν
    have := hN1 p ν hp hpν
    unfold g01c; linarith

include hO1 hO2 hH hN1 hN2 in
/-- `G0` is a clause-2 chart on `N`. -/
theorem g0_c2 (ho1 : 0 ≤ o1) (hn1 : 0 ≤ n1) (hη : 0 ≤ η) (ho2 : 0 ≤ o2) (hn2 : 0 ≤ n2) :
    C2 W (G0 W σ c Go Gn) (SlabS σ lo hi c ch) (g02c o1 o2 n1 n2 η) := by
  intro p μ ν h0 h1 h2 h3
  have hK0 : 0 ≤ K0c o1 n1 η := by unfold K0c; positivity
  have bm : ∀ q, q ∈ SlabS σ lo hi c ch → bp σ c q ∈ SlabS σ lo hi c ch :=
    fun q hq => bp_mem σ lo hi c0 c ch hc0 (by omega) hq
  have hg : g02c o1 o2 n1 n2 η = 3 * o2 + 2 * η + 3 * n2 + 4 * n1 * K0c o1 n1 η := rfl
  rw [gt_G0, gt_G0]
  by_cases hν : ν = σ
  · subst hν
    rw [bp_add_self, bp_add_self]
    refine (conj_diff _ _ _ _).trans ?_
    have a := hN2 p μ ν h0 h1 h2 h3
    have b := hN1 p ν h0 h1
    have hk : frobNorm (((kap0 W ν Go Gn (bp ν c (p + ev μ)) : SU2) : M2) - ((kap0 W ν Go Gn (bp ν c p) : SU2) : M2))
        ≤ K0c o1 n1 η := by
      by_cases hμ : μ = ν
      · subst hμ; rw [bp_add_self, sub_self, frobNorm_zero']; exact hK0
      · rw [bp_add_ne ν c p hμ]
        exact kap0_d1 hc0 hch hO1 hN1 hH (bm p h0) (bp_plane ν c p) hμ (by rw [← bp_add_ne ν c p hμ]; exact bm _ h2)
    have : 2 * frobNorm (((kap0 W ν Go Gn (bp ν c (p + ev μ)) : SU2) : M2) - ((kap0 W ν Go Gn (bp ν c p) : SU2) : M2))
        * frobNorm (((gt W Gn p ν : SU2) : M2) - 1) ≤ 2 * K0c o1 n1 η * n1 :=
      by nlinarith [frobNorm_nonneg (((kap0 W ν Go Gn (bp ν c (p + ev μ)) : SU2) : M2) - ((kap0 W ν Go Gn (bp ν c p) : SU2) : M2)),
        frobNorm_nonneg (((gt W Gn p ν : SU2) : M2) - 1)]
    nlinarith
  · by_cases hμ : μ = σ
    · subst hμ
      rw [bp_add_self, show p + ev μ + ev ν = p + ev ν + ev μ by abel, bp_add_self]
      have g := gauge_step_two (kap0 W μ Go Gn (bp μ c p)) (kap0 W μ Go Gn (bp μ c (p + ev ν)))
        (kap0 W μ Go Gn (bp μ c p)) (kap0 W μ Go Gn (bp μ c (p + ev ν))) (gt W Gn p ν) (gt W Gn (p + ev μ) ν)
      simp only [sub_self, frobNorm_zero', mul_zero, add_zero, zero_add] at g
      have a := hN2 p μ ν h0 h1 h2 h3
      refine g.trans ?_
      nlinarith
    · -- both transverse: plane term + bracket
      set b := bp σ c p with hb
      have hbμ : bp σ c (p + ev μ) = b + ev μ := bp_add_ne σ c p hμ
      have hbν : bp σ c (p + ev ν) = b + ev ν := bp_add_ne σ c p hν
      have hbμν : bp σ c (p + ev μ + ev ν) = b + ev μ + ev ν := by rw [bp_add_ne σ c _ hν, hbμ]
      rw [hbμ, hbν, hbμν]
      have B0 : b ∈ SlabS σ lo hi c ch := bm p h0
      have B1 : b + ev ν ∈ SlabS σ lo hi c ch := by rw [← hbν]; exact bm _ h1
      have B2 : b + ev μ ∈ SlabS σ lo hi c ch := by rw [← hbμ]; exact bm _ h2
      have B3 : b + ev μ + ev ν ∈ SlabS σ lo hi c ch := by rw [← hbμν]; exact bm _ h3
      have pb : b σ = c := bp_plane σ c p
      have pbμ : (b + ev μ) σ = c := by simp [ev_apply_ne (Ne.symm hμ), pb]
      have pbν : (b + ev ν) σ = c := by simp [ev_apply_ne (Ne.symm hν), pb]
      have pbμν : (b + ev μ + ev ν) σ = c := by simp [ev_apply_ne (Ne.symm hν), pbμ]
      -- the plane values
      have Zb : ∀ x, x σ = c → (kap0 W σ Go Gn x * gt W Gn x ν * (kap0 W σ Go Gn (x + ev ν))⁻¹)
          = gt W (G0 W σ c Go Gn) x ν := by
        intro x hx
        rw [gt_G0, bp_of_plane σ hx, bp_of_plane σ (by simp [ev_apply_ne (Ne.symm hν), hx])]
      set K0' := kap0 W σ Go Gn b
      set K1' := kap0 W σ Go Gn (b + ev ν)
      set K2' := kap0 W σ Go Gn (b + ev μ)
      set K3' := kap0 W σ Go Gn (b + ev μ + ev ν)
      -- decomposition
      have dec : ((K2' * gt W Gn (p + ev μ) ν * K3'⁻¹ : SU2) : M2) - ((K0' * gt W Gn p ν * K1'⁻¹ : SU2) : M2)
          = (((gt W (G0 W σ c Go Gn) (b + ev μ) ν : SU2) : M2) - ((gt W (G0 W σ c Go Gn) b ν : SU2) : M2))
            + ((K2' : M2) * (((gt W Gn (p + ev μ) ν : SU2) : M2) - (gt W Gn (b + ev μ) ν : M2)) * (K3' : M2)ᴴ
              - (K0' : M2) * (((gt W Gn p ν : SU2) : M2) - (gt W Gn b ν : M2)) * (K1' : M2)ᴴ) := by
        rw [← Zb b pb, ← Zb (b + ev μ) pbμ]
        simp only [coe_mul, coe_inv, K1', K3']
        rw [show b + ev μ + ev ν = b + ev μ + ev ν from rfl]
        noncomm_ring
      rw [dec]
      refine (frobNorm_add_le _ _).trans ?_
      -- plane term
      have plane : frobNorm (((gt W (G0 W σ c Go Gn) (b + ev μ) ν : SU2) : M2) - ((gt W (G0 W σ c Go Gn) b ν : SU2) : M2))
          ≤ 3 * o2 + 2 * η := by
        rw [g0_plane W σ c Go Gn pbμ hν, g0_plane W σ c Go Gn pb hν]
        refine (prod4_diff _ _ _ _ _ _ _ _).trans ?_
        have hbl := plane_below σ lo hi c0 c ch hc0 (by omega) B0 pb
        have hblμ := plane_below σ lo hi c0 c ch hc0 (by omega) B2 pbμ
        have hblν := plane_below σ lo hi c0 c ch hc0 (by omega) B1 pbν
        have hblμν := plane_below σ lo hi c0 c ch hc0 (by omega) B3 pbμν
        -- Az differences
        have az : ∀ x, x σ = c → x ∈ SlabS σ lo hi c ch → x + ev μ ∈ SlabS σ lo hi c ch →
            frobNorm (((Az W σ Go (x + ev μ) : SU2) : M2) - Az W σ Go x) ≤ o2 := by
          intro x hx hxN hxμN
          have l := plane_below σ lo hi c0 c ch hc0 (by omega) hxN hx
          have lμ := plane_below σ lo hi c0 c ch hc0 (by omega) hxμN (by simp [ev_apply_ne (Ne.symm hμ), hx])
          have := hO2 (x - ev σ - ev σ) μ σ l.2 (by rw [show x - ev σ - ev σ + ev σ = x - ev σ by abel]; exact l.1)
            (by rw [show x - ev σ - ev σ + ev μ = x + ev μ - ev σ - ev σ by abel]; exact lμ.2)
            (by rw [show x - ev σ - ev σ + ev μ + ev σ = x + ev μ - ev σ by abel]; exact lμ.1)
          simp only [Az]
          rw [show x + ev μ - ev σ - ev σ = x - ev σ - ev σ + ev μ by abel]
          exact this
        have a1 : frobNorm ((((Az W σ Go (b + ev μ))⁻¹ : SU2) : M2) - ((Az W σ Go b)⁻¹ : SU2)) ≤ o2 := by
          rw [inv_diff]; exact az b pb B0 B2
        have a2 : frobNorm (((Go (b + ev μ - ev σ) * (hol W (b + ev μ - ev σ) ν σ)⁻¹ * (Go (b + ev μ - ev σ))⁻¹ : SU2) : M2)
            - ((Go (b - ev σ) * (hol W (b - ev σ) ν σ)⁻¹ * (Go (b - ev σ))⁻¹ : SU2) : M2)) ≤ 2 * η := by
          refine (frobNorm_sub_le' _ 1 _).trans ?_
          rw [n_conj, n_inv, frobNorm_sub_comm (1 : M2), n_conj, n_inv]
          have hq1 := hH (b + ev μ - ev σ) ν σ (slab_mono (le_refl _) (by omega) hblμ.1)
            (by rw [show b + ev μ - ev σ + ev ν = b + ev μ + ev ν - ev σ by abel]; exact slab_mono (le_refl _) (by omega) hblμν.1)
            (by rw [show b + ev μ - ev σ + ev σ = b + ev μ by abel]; exact slab_mono (by omega) (le_refl _) B2)
            (by rw [show b + ev μ - ev σ + ev ν + ev σ = b + ev μ + ev ν by abel]; exact slab_mono (by omega) (le_refl _) B3)
          have hq0 := hH (b - ev σ) ν σ (slab_mono (le_refl _) (by omega) hbl.1)
            (by rw [show b - ev σ + ev ν = b + ev ν - ev σ by abel]; exact slab_mono (le_refl _) (by omega) hblν.1)
            (by rw [show b - ev σ + ev σ = b by abel]; exact slab_mono (by omega) (le_refl _) B0)
            (by rw [show b - ev σ + ev ν + ev σ = b + ev ν by abel]; exact slab_mono (by omega) (le_refl _) B1)
          linarith
        have a3 : frobNorm (((gt W Go (b + ev μ - ev σ) ν : SU2) : M2) - ((gt W Go (b - ev σ) ν : SU2) : M2)) ≤ o2 := by
          have := hO2 (b - ev σ) μ ν hbl.1 (by rw [show b - ev σ + ev ν = b + ev ν - ev σ by abel]; exact hblν.1)
            (by rw [show b - ev σ + ev μ = b + ev μ - ev σ by abel]; exact hblμ.1)
            (by rw [show b - ev σ + ev μ + ev ν = b + ev μ + ev ν - ev σ by abel]; exact hblμν.1)
          rw [show b + ev μ - ev σ = b - ev σ + ev μ by abel]; exact this
        have a4 : frobNorm (((Az W σ Go (b + ev μ + ev ν) : SU2) : M2) - Az W σ Go (b + ev ν)) ≤ o2 := by
          rw [show b + ev μ + ev ν = b + ev ν + ev μ by abel]
          exact az (b + ev ν) pbν B1 (by rw [show b + ev ν + ev μ = b + ev μ + ev ν by abel]; exact B3)
        linarith
      -- bracket
      have br := bracket_bound K0' K1' K2' K3' (((gt W Gn p ν : SU2) : M2) - (gt W Gn b ν : M2))
        (((gt W Gn (p + ev μ) ν : SU2) : M2) - (gt W Gn (b + ev μ) ν : M2))
      have kμ0 := kap0_d1 hc0 hch hO1 hN1 hH B0 pb hμ B2
      have kμ1 : frobNorm ((K3' : M2) - (K1' : M2)) ≤ K0c o1 n1 η := by
        have := kap0_d1 hc0 hch hO1 hN1 hH B1 pbν hμ (by rw [show b + ev ν + ev μ = b + ev μ + ev ν by abel]; exact B3)
        simp only [K3', K1']; rw [show b + ev μ + ev ν = b + ev ν + ev μ by abel]; exact this
      have d2 : frobNorm (((gt W Gn (p + ev μ) ν : SU2) : M2) - (gt W Gn (b + ev μ) ν : M2)) ≤ 2 * n1 := by
        refine (frobNorm_sub_le' _ 1 _).trans ?_
        rw [frobNorm_sub_comm (1 : M2)]
        have := hN1 _ ν h2 (by rw [show p + ev μ + ev ν = p + ev μ + ev ν from rfl]; exact h3)
        have := hN1 _ ν B2 B3
        linarith
      have d0 : frobNorm (((gt W Gn p ν : SU2) : M2) - (gt W Gn b ν : M2)) ≤ 2 * n1 := by
        refine (frobNorm_sub_le' _ 1 _).trans ?_
        rw [frobNorm_sub_comm (1 : M2)]
        have := hN1 _ ν h0 h1
        have := hN1 _ ν B0 B1
        linarith
      have dd : frobNorm ((((gt W Gn (p + ev μ) ν : SU2) : M2) - (gt W Gn (b + ev μ) ν : M2))
          - (((gt W Gn p ν : SU2) : M2) - (gt W Gn b ν : M2))) ≤ 2 * n2 := by
        have e : (((gt W Gn (p + ev μ) ν : SU2) : M2) - (gt W Gn (b + ev μ) ν : M2))
            - (((gt W Gn p ν : SU2) : M2) - (gt W Gn b ν : M2))
            = (((gt W Gn (p + ev μ) ν : SU2) : M2) - (gt W Gn p ν : M2))
              - (((gt W Gn (b + ev μ) ν : SU2) : M2) - (gt W Gn b ν : M2)) := by abel
        rw [e]
        refine (frobNorm_sub_le' _ 0 _).trans ?_
        rw [sub_zero, zero_sub, frobNorm_neg]
        have := hN2 p μ ν h0 h1 h2 h3
        have := hN2 b μ ν B0 B1 B2 B3
        linarith
      have t1 : frobNorm ((K2' : M2) - (K0' : M2)) * frobNorm (((gt W Gn (p + ev μ) ν : SU2) : M2) - (gt W Gn (b + ev μ) ν : M2))
          ≤ K0c o1 n1 η * (2 * n1) := mul_le_mul kμ0 d2 (frobNorm_nonneg _) hK0
      have t3 : frobNorm (((gt W Gn p ν : SU2) : M2) - (gt W Gn b ν : M2)) * frobNorm ((K3' : M2) - (K1' : M2))
          ≤ (2 * n1) * K0c o1 n1 η := mul_le_mul d0 kμ1 (frobNorm_nonneg _) (by positivity)
      rw [hg]
      nlinarith

end bounds



end AdalyFormal.UnifLane.Z
