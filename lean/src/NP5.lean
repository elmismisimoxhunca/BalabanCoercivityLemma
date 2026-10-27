import NP4

/-!
# NP5 -- the constrained-harmonic decay on the two-stratum patch at a NON-FLAT configuration (m1_patch_nonflat, 2026-10-14)

**`harmDecay_nf`** : on `G = geomOf ell (i+1) (patchTower i Rg)` (`Rg` block-closed at `ell^{i+1}`, `ell^{i+1} ∣ L μ + 1`), at a
configuration `U` with
* `hU1` : `frobNorm(U b − 1) ≤ θ / ell^{i+1}` on every bond,
* `hU2` : `frobNorm(U(x,μ) − U(x−e_μ,μ)) ≤ θ / ell^{2(i+1)}` (first differences only),
* `hbg`, `hdsum` : background-tower links bounded by `a_j` with `dsum ell a j ≤ D ≤ 1/2` (`j ≤ i+1`),
* `hPoinc` : `‖ν‖² ≤ Pk (ell · ell^i)² ‖D_U ν‖²` on `N(Q'(U))`, `Pk ≥ 1`,
for `12 ell + 10 ≤ d` and every `h ∈ HK G U (Ball w (s + d ell^i))`:
  `gradOn U (Ball w s) h ≤ epsNF ell Pk θ d · (ell^{-(i+1)})² · ‖h‖²`,   `epsNF = CBc(Kq θ)·CAc(ell,Pk,Kq θ)·ell²/rD ell d`.
This is `HarmDecayAt`'s inequality at ONE level `i`, ONE `Rg`, at non-flat `U`; the constant depends on `ell, Pk, θ, d` only
(not on `i`, `Rg`, the torus, `w`, `s`).  **`epsNF_small`** : `epsNF ell Pk θ d → 0` as `d → ∞`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1NonFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist BlockClosed)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.M1Patch (patchTower)
open AdalyFormal.LemIFlat (cc)
open AdalyFormal.M1Decay (Classes patchClasses patchClasses_anc patchClasses_nn pnn lapDir_patch rD rD_pos
  rD_room smoothCut sc_nonneg sc_lip sc_lapR sc_one sc_zero)
open AdalyFormal.M1W2 (HK VK NK suppIn gradOn)

variable {L : PeriodicLatticeExtent}

/-- the non-flat decay constant. -/
noncomputable def epsNF (ell : ℕ) (Pk θ : ℝ) (d : ℕ) : ℝ := CBc (Kq θ) * CAc ell Pk (Kq θ) * (ell : ℝ) ^ 2 / (rD ell d : ℝ)

theorem CBc_pos {θ : ℝ} (hθ : 0 ≤ θ) : 0 < CBc (Kq θ) := by
  unfold CBc; have := Kq_nonneg hθ; linarith

theorem CAc_pos {ell : ℕ} (hell : 1 ≤ ell) {Pk θ : ℝ} (hPk : 1 ≤ Pk) (hθ : 0 ≤ θ) : 0 < CAc ell Pk (Kq θ) := by
  unfold CAc
  have := Kq_nonneg hθ
  have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have : (0 : ℝ) < Pk := by linarith
  positivity

theorem epsNF_nonneg (ell : ℕ) (hell : 1 ≤ ell) {Pk θ : ℝ} (hPk : 1 ≤ Pk) (hθ : 0 ≤ θ) (d : ℕ) :
    0 ≤ epsNF ell Pk θ d := by
  unfold epsNF
  have := CBc_pos hθ; have := CAc_pos hell hPk hθ
  positivity

/-- `epsNF → 0` as `d → ∞`. -/
theorem epsNF_small (ell : ℕ) (hell : 1 ≤ ell) {Pk θ : ℝ} (hPk : 1 ≤ Pk) (hθ : 0 ≤ θ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℕ, 12 * ell + 10 ≤ D ∧ ∀ d, D ≤ d → epsNF ell Pk θ d ≤ δ := by
  set C := CBc (Kq θ) * CAc ell Pk (Kq θ) * (ell : ℝ) ^ 2 with hC
  have hC0 : 0 < C := by
    have := CBc_pos hθ; have := CAc_pos hell hPk hθ
    have : (1 : ℝ) ≤ ell := by exact_mod_cast hell
    positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (C / δ)
  refine ⟨7 * (n + 1) + 12 * ell + 10, by omega, fun d hd => ?_⟩
  have hr : n + 1 ≤ rD ell d := by unfold rD; omega
  have hr' : ((n : ℝ) + 1) ≤ (rD ell d : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < rD ell d := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  unfold epsNF
  rw [← hC, div_le_iff₀ hrpos]
  have h1 : C < δ * n := by have := (div_lt_iff₀ hδ).mp hn; linarith
  nlinarith

open Classical in
/-- **the constrained-harmonic decay at a non-flat configuration, one level**. -/
theorem harmDecay_nf {ell : ℕ} (hell : 2 ≤ ell) (i : ℕ) {Rg : Set (PeriodicLatticeSite L)}
    (hRg : BlockClosed (ell ^ (i + 1)) Rg) (hdvd : ∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1)
    (U : Cfg L) (θ : ℝ) (hθ : 0 ≤ θ)
    (hU1 : ∀ b : Bond L, frobNorm (((U b : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ θ / (ell : ℝ) ^ (i + 1))
    (hU2 : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3), frobNorm (((U (x, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
        - ((U (periodicLatticeShiftBack x μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) ≤ θ / ((ell : ℝ) ^ (i + 1)) ^ 2)
    (a : ℕ → ℝ) (D : ℝ) (hD12 : D ≤ 1 / 2)
    (hbg : ∀ j, j < i + 1 → ∀ y ∈ CoarseLattice L (ell ^ j), ∀ μ : Fin 3,
      frobNorm (((bgTower (geomOf ell (i + 1) (patchTower i Rg)) U j (y, μ) : _) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ a j)
    (hdsum : ∀ j, j ≤ i + 1 → AdalyFormal.BondComposite.dsum ell a j ≤ D)
    (Pk : ℝ) (hPk : 1 ≤ Pk)
    (hPoinc : ∀ ν ∈ NQp (geomOf ell (i + 1) (patchTower i Rg)) U,
      ‖ν‖ ^ 2 ≤ Pk * ((ell : ℝ) * ((ell ^ i : ℕ) : ℝ)) ^ 2 * ‖gradL2 U ν‖ ^ 2)
    (d : ℕ) (hd : 12 * ell + 10 ≤ d) (w : PeriodicLatticeSite L) (s : ℕ) (h : SiteL2 L)
    (hh : h ∈ HK (geomOf ell (i + 1) (patchTower i Rg)) U (Ball w (s + d * ell ^ i))) :
    gradOn U (Ball w s) h ≤ epsNF ell Pk θ d * (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 * ‖h‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  have hell1 : 1 ≤ ell := by omega
  set B := ell ^ i with hBdef
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hell0
  set G := geomOf ell (i + 1) (patchTower i Rg) with hG
  set K := Ball w (s + d * ell ^ i) with hK
  obtain ⟨hR, hperp⟩ := Submodule.mem_inf.mp hh
  obtain ⟨μ, hμN, hμh⟩ := Submodule.mem_map.mp hR
  have hhμ : h = lapFull U μ := by rw [← hμh]; exact lapDir_patch ell i Rg _ μ
  subst hhμ
  set Cl := patchClasses hell0 hRg hdvd with hCl
  set kk := lapFull U (lapFull U μ) with hkk
  -- orthogonality of Δh to N_K
  have hk : ∀ f ∈ NK G U K, ⟪kk, f⟫ = 0 := by
    intro f hf
    have hV : lapDir G U f ∈ VK G U K := Submodule.mem_map_of_mem hf
    have h0 := (Submodule.mem_orthogonal _ _).mp hperp _ hV
    rw [hkk, lapFull_symm, real_inner_comm]
    rw [lapDir_patch] at h0
    exact h0
  have hP : ‖μ‖ ^ 2 ≤ Pk * ((ell : ℝ) * B) ^ 2 * ‖gradL2 U μ‖ ^ 2 := hPoinc μ hμN
  have hperpC : ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) → ∑ z ∈ Cl.cls x, ⟪kk z, μ z⟫ = 0 :=
    fun x hx => perp_class hell0 hRg hdvd U K kk hk μ hμN x hx
  -- the per-class bound
  have hkC : 24 ≤ B → ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) →
      ∑ z ∈ Cl.cls x, ‖kk z‖ ^ 2 ≤ Kq θ ^ 2 * ((Cl.nn x : ℝ) ^ 4)⁻¹ * ∑ z ∈ Cl.cls x, ‖lapFull U μ z‖ ^ 2 := by
    intro hB24 x hx
    obtain ⟨c, hc⟩ := rep_of_perp hell0 hRg hdvd U K kk hk x hx
    have hcls : Cl.cls x = blockOf (cc ell i Rg x) (pnn ell i Rg x) := by
      rw [Classes.cls_eq_block, patchClasses_anc, patchClasses_nn]
    have hn24 : 24 ≤ pnn ell i Rg x := le_trans hB24 (Cl.nn_ge x)
    have hfit : ∀ μ, (cc ell i Rg x μ).val + pnn ell i Rg x ≤ L μ + 1 := Cl.fit x
    have hnle : ((pnn ell i Rg x : ℕ) : ℝ) ≤ (ell : ℝ) ^ (i + 1) := by
      have : pnn ell i Rg x ≤ ell ^ (i + 1) := by
        have h1 := Cl.nn_le x
        have : ell * ell ^ i = ell ^ (i + 1) := by ring
        rw [← this]; exact h1
      exact_mod_cast this
    have hnpos : (0 : ℝ) < (pnn ell i Rg x : ℕ) := by
      have : (24 : ℝ) ≤ (pnn ell i Rg x : ℕ) := by exact_mod_cast hn24
      linarith
    have hV1 : ∀ z ∈ blockOf (cc ell i Rg x) (pnn ell i Rg x), ∀ μ : Fin 3,
        frobNorm (((U (z, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ θ / (pnn ell i Rg x : ℕ) ∧
        frobNorm (((U (periodicLatticeShiftBack z μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
          ≤ θ / (pnn ell i Rg x : ℕ) := by
      intro z _ μ
      have hmono : θ / (ell : ℝ) ^ (i + 1) ≤ θ / (pnn ell i Rg x : ℕ) :=
        div_le_div_of_nonneg_left hθ hnpos hnle
      exact ⟨(hU1 _).trans hmono, (hU1 _).trans hmono⟩
    have hV2 : ∀ z ∈ blockOf (cc ell i Rg x) (pnn ell i Rg x), ∀ μ : Fin 3,
        frobNorm (((U (z, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
          - ((U (periodicLatticeShiftBack z μ, μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ))
          ≤ θ / ((pnn ell i Rg x : ℕ) : ℝ) ^ 2 := by
      intro z _ μ
      have hmono : θ / ((ell : ℝ) ^ (i + 1)) ^ 2 ≤ θ / ((pnn ell i Rg x : ℕ) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left hθ (by positivity) (pow_le_pow_left₀ hnpos.le hnle 2)
      exact (hU2 z μ).trans hmono
    have hb := bump_cov (cc ell i Rg x) (pnn ell i Rg x) hn24 hfit U (lapFull U μ)
      (rowx (ell := ell) (i := i) (Rg := Rg) U x : SiteL2 L →ₗ[ℝ] SuTwo) c
      (fun f hf => hc f (fun z hz => hf z (by rw [← hcls]; exact hz)))
      (fun f => by
        have := row_norm hell0 hRg hdvd U x f
        rw [hcls] at this; exact this)
      D hD12
      (fun f => by
        have := row_drift hell0 hRg hdvd U a D hbg hdsum x f
        rw [hcls] at this; exact this)
      θ hθ hV1 hV2
    rw [hcls]
    have e : Kq θ ^ 2 * (((pnn ell i Rg x : ℕ) : ℝ) ^ 4)⁻¹ *
        ∑ z ∈ blockOf (cc ell i Rg x) (pnn ell i Rg x), ‖lapFull U μ z‖ ^ 2
        = Kq θ ^ 2 * ((((pnn ell i Rg x : ℕ) : ℝ) ^ 4)⁻¹ *
          ∑ z ∈ blockOf (cc ell i Rg x) (pnn ell i Rg x), ‖lapFull U μ z‖ ^ 2) := by ring
    show _ ≤ Kq θ ^ 2 * (((Cl.nn x : ℕ) : ℝ) ^ 4)⁻¹ * _
    rw [show Cl.nn x = pnn ell i Rg x from rfl, e]
    exact hb
  -- room arithmetic
  set r := rD ell d with hr
  have hr1 : 1 ≤ r := rD_pos hd
  have hroom : 7 * r + 12 * ell + 3 ≤ d := by
    rcases rD_room (ell := ell) (d := d) with h1 | h1
    · exact h1
    · omega
  have hroomB : 7 * (r * B) + 12 * (ell * B) + 3 * B ≤ d * B := by
    have := Nat.mul_le_mul_right B hroom
    nlinarith [this]
  have hellB : B ≤ ell * B := Nat.le_mul_of_pos_left B hell0
  set R := r * B with hRdef
  have hR0 : 0 < R := Nat.mul_pos (by omega) (by omega)
  have hRB : B ≤ R := Nat.le_mul_of_pos_left B (by omega)
  set ρY := s + 2 + B + 6 * (ell * B) with hρY
  have hKq := Kq_nonneg hθ
  have hint := ClassesC.interior_bound_cov Cl U hell hB μ (Kq θ) hKq K hkC w s ρY le_rfl (by
    intro x hx z hz
    have h1 := pdist_triangle w x z
    have h2 : pdist x z ≤ 6 * Cl.nn x := Cl.pdist_in_cls x z hz
    have h3 : Cl.nn x ≤ ell * B := Cl.nn_le x
    show pdist w z ≤ s + d * B
    omega)
  set a' := ρY + 3 * (R - 1) with ha'
  set g := smoothCut w a' R R with hg
  have hS := ClassesC.S_bound_cov Cl U hell hB μ Pk (Kq θ) hPk hKq hP K hperpC hkC g R hR0 hRB
    (sc_nonneg w a' R R) (sc_lip w a' R R hR0 hR0) (fun x => sc_lapR w a' R R hR0 hR0 x) (by
      intro x hx z hz
      have hxw : pdist w x ≤ a' + R + 3 * (R - 1) := by
        by_contra hc; exact hx (sc_zero w a' R R hR0 hR0 x (by omega))
      have h1 := pdist_triangle w x z
      have h2 : pdist x z ≤ 6 * Cl.nn x := Cl.pdist_in_cls x z hz
      have h3 : Cl.nn x ≤ ell * B := Cl.nn_le x
      show pdist w z ≤ s + d * B
      omega)
  have hcmp : ∑ x, (if pdist w x ≤ ρY then ‖lapFull U μ x‖ ^ 2 else 0)
      ≤ ∑ x, g x * ‖lapFull U μ x‖ ^ 2 := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    split_ifs with hx
    · rw [show g x = 1 from sc_one w a' R R hR0 hR0 ρY le_rfl x hx, one_mul]
    · exact mul_nonneg (sc_nonneg w a' R R x) (sq_nonneg _)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hCB := CBc_pos hθ
  have hCA := CAc_pos hell1 hPk hθ
  have hRr : ((B : ℝ) / R) = 1 / r := by
    rw [hRdef]; push_cast; field_simp
  have hfin : CBc (Kq θ) / (B : ℝ) ^ 2 * (CAc ell Pk (Kq θ) * ((B : ℝ) / R) * ‖lapFull U μ‖ ^ 2)
      = epsNF ell Pk θ d * (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 * ‖lapFull U μ‖ ^ 2 := by
    rw [hRr]
    unfold epsNF
    rw [← hr]
    have hB' : (B : ℝ) = (ell : ℝ) ^ i := by rw [hBdef, Nat.cast_pow]
    rw [hB']
    have : (0 : ℝ) < ell := by exact_mod_cast hell0
    field_simp
    ring
  calc gradOn U (Ball w s) (lapFull U μ)
      ≤ CBc (Kq θ) / (B : ℝ) ^ 2 * ∑ x, (if pdist w x ≤ ρY then ‖lapFull U μ x‖ ^ 2 else 0) := hint
    _ ≤ CBc (Kq θ) / (B : ℝ) ^ 2 * (CAc ell Pk (Kq θ) * ((B : ℝ) / R) * ‖lapFull U μ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hcmp.trans hS) (by positivity)
    _ = _ := hfin

end AdalyFormal.M1NonFlat

#print axioms AdalyFormal.M1NonFlat.epsNF_nonneg
#print axioms AdalyFormal.M1NonFlat.epsNF_small
#print axioms AdalyFormal.M1NonFlat.harmDecay_nf
