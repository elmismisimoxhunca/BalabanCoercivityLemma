import SG2
import PP4
import OGP0

/-!
# SG3 -- good anchors: `Deep` and `Shallow` give a chart (lane m2_fields123_20261015)

`AnchorChart12 x r` : one `M1Regular12` configuration `V` and a gauge `g` with `U^g = V` at every bond based in `Ball x r`.
For a site `x ∈ Ω_j \ Ω_{j+1}`:
* `Deep`    : the `7 M ℓ^j`-box of `x` lies in `Ω_j`            ⟹ index-`j` class cube (`chart_deep`);
* `Shallow` : `j = i+1` and some `w`, `pdist x w ≤ 5 M ℓ^i`, is not in `Ω_j` ⟹ index-`i` class cube (`chart_shallow`).
Both need only `R ≥ 26` (the collar `hcol` of `Admissible`).  The complement (neither) is the BAND.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap12

open AdalyFormal.M2F123
open AdalyFormal.OneGap12

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt)

/-- one `M1Regular12` chart on a ball -/
def AnchorChart12 {L : PeriodicLatticeExtent} (ell M k : ℕ) (S : Tower L) (U : LinkCfg L) (α₀ η : ℝ)
    (x : PeriodicLatticeSite L) (r : ℕ) : Prop :=
  ∃ (g : GaugeFn L) (V : LinkCfg L),
    AdalyFormal.OneGap12.M1Regular12 ell M 12 k S ((ell : ℝ) ^ 3 * (2 * α₀)) η V ∧
    AgreeAt (Ball x r) (periodicGaugeTransform g U) V

/-- the `7 B`-box around `x` lies in `Ω_j` -/
def DeepAt12 {L : PeriodicLatticeExtent} (ell M : ℕ) (S : Tower L) (j : ℕ) (x : PeriodicLatticeSite L) : Prop :=
  ∀ x'' : PeriodicLatticeSite L, (∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * (M * ell ^ j)) → x'' ∈ S.Om j

/-- some point within `5 M ℓ^i` of `x` is outside `Ω_{i+1}` -/
def ShallowAt12 {L : PeriodicLatticeExtent} (ell M : ℕ) (S : Tower L) (i : ℕ) (x : PeriodicLatticeSite L) : Prop :=
  ∃ w : PeriodicLatticeSite L, pdist x w ≤ 5 * (M * ell ^ i) ∧ w ∉ S.Om (i + 1)

theorem pdist_le_box12 {L : PeriodicLatticeExtent} {B : ℕ} (x x'' : PeriodicLatticeSite L)
    (h : ∀ σ : Fin 3, pcd (L σ + 1) (x σ).val (x'' σ).val ≤ 7 * B) : pdist x x'' ≤ 21 * B := by
  unfold pdist
  calc ∑ μ : Fin 3, pcd (L μ + 1) (x μ).val (x'' μ).val ≤ ∑ _μ : Fin 3, 7 * B :=
        Finset.sum_le_sum (fun σ _ => h σ)
    _ = 21 * B := by simp; ring

theorem placed_deep12 {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M)
    {S : Tower L} (hS : Admissible ell M R k S) (hR : 26 ≤ R) {j : ℕ} (hj : j ≤ k) (x : PeriodicLatticeSite L)
    (hx1 : x ∉ S.Om (j + 1)) (hdeep : DeepAt12 ell M S j x)
    (r : ℕ) (hr : r + 128 * ell ^ j + 5 ≤ 5 * (M * ell ^ j)) :
    PlacedAt ell M k S x r := by
  have hell0 : 0 < ell := by omega
  have hB : 0 < M * ell ^ j := Nat.mul_pos hM (pow_pos hell0 j)
  refine placed_gen hell0 hM hS hj x hdeep ?_ x (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega) hx1 r hr
  intro x'' hx''
  intro hmem
  by_cases hjk : j + 1 ≤ k
  · have h1 := hS.2.2.2.2.1 (j + 1) hjk x hx1 x'' hmem
    have h2 := pdist_le_box12 x x'' hx''
    have h3 : bigSide M ell (j + 1) = ell * (M * ell ^ j) := by unfold bigSide; ring
    rw [h3] at h1
    have h4 : 21 * (M * ell ^ j) ≤ R * (ell * (M * ell ^ j)) := by
      have : 21 ≤ R * ell := by nlinarith
      nlinarith
    omega
  · have := hS.2.1 (j + 2) (by omega)
    rw [this] at hmem
    exact hmem

theorem placed_shallow12 {ell M R k : ℕ} {L : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M)
    {S : Tower L} (hS : Admissible ell M R k S) (hR : 26 ≤ R) {i : ℕ} (hi : i + 1 ≤ k) (x : PeriodicLatticeSite L)
    (hx : x ∈ S.Om (i + 1)) (hsh : ShallowAt12 ell M S i x)
    (r : ℕ) (hr : r + 128 * ell ^ i + 5 ≤ 5 * (M * ell ^ i)) :
    PlacedAt ell M k S x r := by
  have hell0 : 0 < ell := by omega
  have hB : 0 < M * ell ^ i := Nat.mul_pos hM (pow_pos hell0 i)
  obtain ⟨w, hw, hwO⟩ := hsh
  refine placed_gen hell0 hM hS (by omega : i ≤ k) x ?_ ?_ w hw hwO r hr
  · intro x'' hx''
    by_contra hno
    have h1 := hS.2.2.2.2.1 i (by omega) x'' hno x hx
    have h2 := pdist_le_box12 x x'' hx''
    rw [AdalyFormal.StatementLaneR8.pdist_comm] at h2
    have h3 : bigSide M ell i = M * ell ^ i := rfl
    rw [h3] at h1
    have : 21 * (M * ell ^ i) ≤ R * (M * ell ^ i) := by nlinarith
    omega
  · intro x'' hx'' hmem
    have h1 := hS.2.2.2.2.1 (i + 1) hi w hwO x'' hmem
    have h2 := pdist_le_box12 x x'' hx''
    have h3 := AdalyFormal.StatementLaneR8.pdist_triangle w x x''
    have h4 : bigSide M ell (i + 1) = ell * (M * ell ^ i) := by unfold bigSide; ring
    rw [h4] at h1
    have h5 := AdalyFormal.StatementLaneR8.pdist_comm x w
    have : 26 * (M * ell ^ i) ≤ R * (ell * (M * ell ^ i)) := by
      have : 26 ≤ R * ell := by nlinarith
      nlinarith
    omega

end AdalyFormal.OneGap12
#print axioms AdalyFormal.OneGap12.placed_deep12
#print axioms AdalyFormal.OneGap12.placed_shallow12
