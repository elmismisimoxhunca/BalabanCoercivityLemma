import MS9
import ZR8Data
import M1B

/-!
# DK1 -- WRAP-FREE cone regions for `link_tower_na_loc`, and fine sites near `Λ` lie in `Ω_k` (KD sub-lane, 2026-10-13)

Lane C's MS8 (`goodPl_of_region`, `goodL_of_region`, `goodBd_of_region`) states the cones of NB25 `link_tower_na_loc` inside a
FORWARD OFFSET box and needs the no-wrap condition `4ℓ^l < L_σ + 1`.  At the top level `l = k` that condition fails on the
unit torus `Lu_σ + 1 = 4`, `ℓ = 2` (allowed by `TorusOK`).  Here the same cones are placed in an `ℓ¹` (`pdist`) BALL, combined
with the triangle inequality, so only the divisibility `ℓ^l ∣ L_σ + 1` is used:
* `goodPl_pd` (radius `12ℓ^l`), `goodL_pd` (radius `ℓ^l`, same direction), `goodBd_pd` (radius `12ℓ^l`).
Unit/fine distances:
* `pcd_blk` : `s · pcd_N(a, ⌊b/s⌋) ≤ pcd_{Ns}(s a, b) + s`;
* `blk` (the unit site of the fine `ℓ^k`-block of `x`), `pdist_blk` : `ℓ^k · |z − blk x| ≤ |embY z − x| + 3ℓ^k`;
* **`deep_mem`** : `y ∈ Λ`, `|embY z − x| ≤ D ℓ^k`, `|y − z| + D + 3 ≤ R M` ⟹ `x ∈ Ω_k` (lane B `lam_deep`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DK

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist pcd scaleUp LambdaOK)
open AdalyFormal.StatementLaneG (LambdaOK2)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.CurvBlock (off Box GoodPl GoodBd goodL mem_pathBonds_rep box_stair block_offsets gamma_eq off_self)
open AdalyFormal.IngredientFamilyR2 (embY embY_val)

variable {L : PeriodicLatticeExtent}

theorem pdist_le_sumoff (y z : PeriodicLatticeSite L) : pdist y z ≤ ∑ σ : Fin 3, off y z σ := by
  have h := AdalyFormal.M1Site.pdist_le_off y z
  rw [pdist_comm] at h; exact h

/-- the plaquette cone in the `pdist` ball of radius `12ℓ^l` -/
theorem goodPl_pd (ell : ℕ) (hell : 2 ≤ ell) (R : PeriodicLatticeSite L → Prop) :
    ∀ (l : ℕ) (y : PeriodicLatticeSite L), (∀ w, pdist y w ≤ 12 * ell ^ l → R w) → GoodPl ell R l y := by
  intro l
  induction l with
  | zero =>
    intro y h
    exact h y (by rw [pdist_self]; omega)
  | succ l ih =>
    intro y h z _ hbox
    refine ih z (fun w hw => h w ?_)
    have h1 := pdist_le_sumoff y z
    rw [Fin.sum_univ_three] at h1
    have hb0 := (hbox 0).2
    have hb1 := (hbox 1).2
    have hb2 := (hbox 2).2
    have h3 := pdist_triangle y z w
    have hp : 1 ≤ ell ^ l := Nat.one_le_pow _ _ (by omega)
    have hq : ell ^ l * 2 ≤ ell ^ l * ell := Nat.mul_le_mul_left _ hell
    rw [pow_succ]
    omega

/-- the straight-link cone in the `pdist` ball of radius `ℓ^l` -/
theorem goodL_pd (ell : ℕ) (hell : 2 ≤ ell) (Rl : PeriodicLatticeEdge L → Prop) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L),
      (∀ b : PeriodicLatticeEdge L, b.2 = c.2 → pdist c.1 b.1 ≤ ell ^ l → Rl b) → goodL ell Rl l c := by
  intro l
  induction l with
  | zero =>
    intro c h
    exact h c rfl (by rw [pdist_self]; omega)
  | succ l ih =>
    intro c h b hb
    obtain ⟨t, ht, rfl⟩ := mem_pathBonds_rep (ell ^ l) c.2 ell c.1 b hb
    refine ih _ (fun b' hb'2 hb' => h b' hb'2 ?_)
    have h1 := pdist_coarseShift_le c.1 (ell ^ l * t) c.2
    have h2 := pdist_triangle c.1 (coarseShift c.1 (ell ^ l * t) c.2) b'.1
    have hst : ell ^ l * t + ell ^ l ≤ ell ^ l * ell := by
      have := Nat.mul_le_mul_left (ell ^ l) (Nat.succ_le_of_lt ht); rwa [Nat.mul_succ] at this
    have hb'' : pdist (coarseShift c.1 (ell ^ l * t) c.2) b'.1 ≤ ell ^ l := hb'
    rw [pow_succ]
    omega

/-- the bond cone (links and ladder plaquettes) in the `pdist` ball of radius `12ℓ^l`; only divisibility is used. -/
theorem goodBd_pd (ell : ℕ) (hell : 2 ≤ ell) (R : PeriodicLatticeSite L → Prop) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L), c.1 ∈ CoarseLattice L (ell ^ l) → (∀ σ, ell ^ l ∣ L σ + 1) →
      (∀ w, pdist c.1 w ≤ 12 * ell ^ l → R w) → GoodBd ell R l c := by
  intro l
  induction l with
  | zero => intro c _ _ _; trivial
  | succ l ih =>
    intro c hc hdvd h
    have hell0 : 0 < ell := by omega
    have hp : 1 ≤ ell ^ l := Nat.one_le_pow _ _ hell0
    have hq : ell ^ l * 2 ≤ ell ^ l * ell := Nat.mul_le_mul_left _ hell
    have hsucc : ell ^ (l + 1) = ell ^ l * ell := pow_succ ell l
    have hdvdl : ∀ σ, ell ^ l ∣ L σ + 1 := fun σ => Dvd.dvd.trans (pow_dvd_pow ell (Nat.le_succ l)) (hdvd σ)
    have hcl : c.1 ∈ CoarseLattice L (ell ^ l) := by
      rw [mem_CoarseLattice] at hc ⊢
      intro ν
      exact Nat.mod_eq_zero_of_dvd (dvd_trans (pow_dvd_pow ell (Nat.le_succ l)) (Nat.dvd_of_mod_eq_zero (hc ν)))
    have hfit : ∀ σ, (c.1 σ).val + ell ^ l * ell ≤ L σ + 1 := by
      have := AdalyFormal.Balaban.PoincareBridge.coarseLattice_fits hdvd hc
      intro σ; have := this σ; rwa [hsucc] at this
    have hLe : ∀ σ, ell ^ l * ell ≤ L σ + 1 := fun σ => by
      have := Nat.le_of_dvd (Nat.succ_pos _) (hdvd σ); rwa [hsucc] at this
    refine ⟨fun b hb => ?_, fun x hx t ht => ?_⟩
    · -- straight bonds
      obtain ⟨t, ht, rfl⟩ := mem_pathBonds_rep (ell ^ l) c.2 ell c.1 b hb
      have hst : ell ^ l * t + ell ^ l ≤ ell ^ l * ell := by
        have := Nat.mul_le_mul_left (ell ^ l) (Nat.succ_le_of_lt ht); rwa [Nat.mul_succ] at this
      refine ih _ (AdalyFormal.M1Site.coarseShift_mul_mem_coarse (ell ^ l) t hdvdl c.1 hcl c.2) hdvdl
        (fun w hw => h w ?_)
      have h1 := pdist_coarseShift_le c.1 (ell ^ l * t) c.2
      have h2 := pdist_triangle c.1 (coarseShift c.1 (ell ^ l * t) c.2) w
      have hw' : pdist (coarseShift c.1 (ell ^ l * t) c.2) w ≤ 12 * ell ^ l := hw
      rw [hsucc]
      omega
    · -- ladder plaquettes
      set s := ell ^ l with hs
      have hxo := block_offsets s ell c.1 x hfit hx
      have hmul : ∀ σ, s * (off c.1 x σ / s) = off c.1 x σ := fun σ => Nat.mul_div_cancel' (hxo σ).1
      set B := s * ell - s with hB
      have hBL : ∀ ρ, B < L ρ + 1 := fun ρ => by have := hLe ρ; omega
      have hbox0 : Box c.1 s B c.1 := fun σ => by rw [off_self]; exact ⟨dvd_zero _, Nat.zero_le _⟩
      obtain ⟨b, hb, m, hm, hbt⟩ := AdalyFormal.M1Site.ladPlaqs_base s c.2 ell
        (AdalyFormal.Balaban.TowerLawCov.coarseGammaPath s c.1 x) c.1 t ht
      rw [gamma_eq] at hb
      have hbB := box_stair c.1 c.1 s B _ _ _ hbox0
        (by rw [off_self, hmul]; have := (hxo 2).2; omega)
        (by rw [off_self, hmul]; have := (hxo 1).2; omega)
        (by rw [off_self, hmul]; have := (hxo 0).2; omega) hBL b hb
      have hsm : s * m + s ≤ s * ell := by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hm); rwa [Nat.mul_succ] at this
      refine goodPl_pd ell hell R l t.1 (fun w hw => h w ?_)
      have h1 := pdist_le_sumoff c.1 b.1
      rw [Fin.sum_univ_three] at h1
      have hb0 := (hbB 0).2
      have hb1 := (hbB 1).2
      have hb2 := (hbB 2).2
      have h2 : pdist b.1 t.1 ≤ s * m := by rw [hbt]; exact pdist_coarseShift_le b.1 (s * m) c.2
      have h3 := pdist_triangle c.1 b.1 t.1
      have h4 := pdist_triangle c.1 t.1 w
      rw [hsucc]
      omega

/-! ## unit vs fine distances -/

theorem pcd_blk (N s a b : ℕ) (hs : 0 < s) (ha : a < N) (hb : b < N * s) :
    s * pcd N a (b / s) ≤ pcd (N * s) (s * a) b + s := by
  have hq : b / s < N := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hb)
  have hbq : b = s * (b / s) + b % s := (Nat.div_add_mod b s).symm
  have hr : b % s < s := Nat.mod_lt _ hs
  generalize b / s = q at hq hbq ⊢
  generalize b % s = r at hbq hr
  subst hbq
  unfold pcd
  rw [← Nat.mul_min_mul_left]
  have hsN : s * N = N * s := mul_comm _ _
  by_cases h : a ≤ q
  · have h1 : s * a ≤ s * q := Nat.mul_le_mul_left _ h
    have e1 : s * (q - a) = s * q - s * a := mul_tsub s q a
    have e2 : s * (N - (q - a)) = s * N - s * (q - a) := mul_tsub s N (q - a)
    have h2 : s * q + s ≤ s * N := by
      have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hq); rwa [Nat.mul_succ] at this
    rw [if_pos h, if_pos (show s * a ≤ s * q + r by omega), e2, e1]
    omega
  · push Not at h
    have h1 : s * q + s ≤ s * a := by
      have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt h); rwa [Nat.mul_succ] at this
    have e1 : s * (a - q) = s * a - s * q := mul_tsub s a q
    have e2 : s * (N - (a - q)) = s * N - s * (a - q) := mul_tsub s N (a - q)
    have h2 : s * a + s ≤ s * N := by
      have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt ha); rwa [Nat.mul_succ] at this
    rw [if_neg (show ¬ a ≤ q by omega), if_neg (show ¬ s * a ≤ s * q + r by omega), e2, e1]
    omega

/-- the unit site of the fine `ℓ^k`-block of `x` -/
def blk (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    PeriodicLatticeSite Lu :=
  fun μ => ⟨(x μ).val / ell ^ k, by
    have h : (x μ).val < (Lu μ + 1) * ell ^ k :=
      lt_of_lt_of_eq (x μ).isLt (AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell μ)
    exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at h)⟩

theorem blk_val (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (μ : Fin 3) : ((blk ell k Lu hell x) μ).val = (x μ).val / ell ^ k := rfl

theorem pdist_blk (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (z : PeriodicLatticeSite Lu)
    (x : PeriodicLatticeSite (scaleUp ell k Lu)) :
    ell ^ k * pdist z (blk ell k Lu hell x) ≤ pdist (embY ell k Lu hell z) x + 3 * ell ^ k := by
  have hs : 0 < ell ^ k := pow_pos hell k
  have hpt : ∀ μ : Fin 3, ell ^ k * pcd (Lu μ + 1) (z μ).val ((blk ell k Lu hell x) μ).val
      ≤ pcd (scaleUp ell k Lu μ + 1) ((embY ell k Lu hell z) μ).val (x μ).val + ell ^ k := by
    intro μ
    have hx : (x μ).val < (Lu μ + 1) * ell ^ k :=
      lt_of_lt_of_eq (x μ).isLt (AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell μ)
    have h := pcd_blk (Lu μ + 1) (ell ^ k) (z μ).val (x μ).val hs (z μ).isLt hx
    have e : ∀ A B : ℕ, pcd (scaleUp ell k Lu μ + 1) A B = pcd ((Lu μ + 1) * ell ^ k) A B := fun A B => by
      rw [AdalyFormal.GaugeCov.scaleUp_succ ell k Lu hell μ]
    rw [blk_val, embY_val, e]
    exact h
  unfold pdist
  rw [Finset.mul_sum, Fin.sum_univ_three, Fin.sum_univ_three]
  have := hpt 0; have := hpt 1; have := hpt 2
  omega

/-- **fine sites near (a unit site near) `Λ` lie in `Ω_k`.** -/
theorem deep_mem {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    {Lam : Set (PeriodicLatticeSite Lu)} (hA : Admissible ell M R k S) (hL : LambdaOK2 ell M R k S Lam) (hell : 0 < ell)
    {y z : PeriodicLatticeSite Lu} (hy : y ∈ Lam) (D : ℕ) (hroom : pdist y z + D + 3 ≤ R * M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hx : pdist (embY ell k Lu hell z) x ≤ D * ell ^ k) :
    x ∈ S.Om k := by
  have hs : 0 < ell ^ k := pow_pos hell k
  have h1 := pdist_blk ell k Lu hell z x
  have h2 : ell ^ k * pdist z (blk ell k Lu hell x) ≤ ell ^ k * (D + 3) := by
    rw [Nat.mul_add, mul_comm (ell ^ k) D]; omega
  have h3 := Nat.le_of_mul_le_mul_left h2 hs
  have h4 := pdist_triangle y z (blk ell k Lu hell x)
  exact AdalyFormal.M1.lam_deep (y' := blk ell k Lu hell x) hA hL.1 hell hy (by omega) (fun μ => rfl)

#print axioms pdist_le_sumoff
#print axioms goodPl_pd
#print axioms goodL_pd
#print axioms goodBd_pd
#print axioms pcd_blk
#print axioms blk
#print axioms blk_val
#print axioms pdist_blk
#print axioms deep_mem

end AdalyFormal.M1DK
