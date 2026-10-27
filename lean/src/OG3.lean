import OG2

/-!
# OG3 -- the cut-off field satisfies the clause-3-free bounds (lane m2_onegap_20261015)
`vcutA_M1Bounds12` : `M1Bounds12 S ell M f k (ℓ³·2α₀) η (cutA χ A)` on EVERY bond of the torus, from `CubeData12` on a window box and a cutoff `CutSpec`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.OneGap

open AdalyFormal.M2Bridge
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1 (bstrat)

variable {L : PeriodicLatticeExtent}
variable {ell M R f k i : ℕ} {S : Tower L} {α₀ η : ℝ} {sites : Set (PeriodicLatticeSite L)} {A : Bond L → M2m}
  {χ : PeriodicLatticeSite L → ℝ} {τ1 τ2 : ℝ}

theorem vcutA_M1Bounds12 (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    (hq : ∀ e : Bond L, CubeBond sites e → bstrat S k e ≤ i + 1) (hd : CubeData12 ell M f α₀ η sites i A)
    (hc : CutSpec sites χ τ1 τ2) (h1 : 64 * τ1 * (ell : ℝ) ^ i ≤ 1) :
    AdalyFormal.OneGap12.M1Bounds12 S ell M f k ((ell : ℝ) ^ 3 * (2 * α₀)) η (cutA χ A) :=
  ⟨vcut_ht hc hd, vcut_c1 hA hell hf hM hα hη hq hd hc, vcut_c2 hA hell hf hM hα hη hq hd hc h1, trivial⟩

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.vcutA_M1Bounds12
