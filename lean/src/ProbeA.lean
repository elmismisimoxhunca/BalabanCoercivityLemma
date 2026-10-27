import CaT2d
import NtFinal
import NVC7
set_option autoImplicit false
set_option maxHeartbeats 16000000
open AdalyFormal.NcwdhStrong AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.Target.ClayStatement

-- (1) only-class-differs: coverage-free body implies the covering body, by pure unfolding + hU.2
theorem probe_nc_imp_cov (c : ℕ) (h : P428Target8NCWDHc c) : CovAssume.P428Target8NCWDHcov c := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hb⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hR⟩ := hb m hm
  refine ⟨R₀, fun R hR' => ?_⟩
  obtain ⟨h1, a₀, ha₀, γ₀, hγ, hc⟩ := hR R hR'
  exact ⟨h1, a₀, ha₀, γ₀, hγ, fun k hk Lu α₀ hα hle => CovAssume.coercNC_imp_cov (hc k hk Lu α₀ hα hle)⟩
-- (2) the coverage-free statement is REFUTED, the coverage one proved: a real separation
theorem probe_sep (c : ℕ) (hc : 10 ≤ c) : CovAssume.P428Target8NCWDHcov c ∧ ¬ P428Target8NCWDHc c :=
  ⟨CovAssume.p428Target8NCWDHcov_of_total c hc, not_P428Target8NCWDHc c hc⟩
-- (3) non-vacuity applies: an in-class point at the T1 instance exists (ClassCoupled, same c, same M=ell^m)
theorem probe_nv {ell m R c : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) (hc : 10 ≤ c) (hR : 1 ≤ R) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ (k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
      (U : AdalyFormal.Balaban.CoercUMainDesigned.LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ),
      1 ≤ k ∧ TorusOK ell (ell ^ m) Lu ∧ Admissible ell (ell ^ m) R k S ∧ LambdaOK2 ell (ell ^ m) R k S Lam ∧ 0 < α₀ ∧
      ((c:ℕ):ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧ ClassCoupled ell (ell ^ m) c k S α₀ ((ell : ℝ) ^ k)⁻¹ U := by
  obtain ⟨k, Lu, S, Lam, U, α₀, Bt, hk, hT, hA, hL, hα, hαS, hCC, -⟩ := AdalyFormal.NonVacC.headline_regime_nonvacuousC (R := R) hell hm hc hR ha₀
  exact ⟨k, Lu, S, Lam, U, α₀, by omega, hT, hA, hL, hα, hαS, hCC⟩
-- (4) the covered (T2) side body, the two bodies' hypotheses: Cov implies Sites-body's statement fails but Cov holds; check Sites <-> Cov differ only by CovPlaqF
theorem probe_cov_imp_sites_hyp {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : AdalyFormal.Balaban.CoercUMainDesigned.LinkCfg L} :
  MXQ.Total.ClassCoupledF ell M (NcwdhFam.constFam c L) k S α₀ η U ↔
    (NcwdhFam.CovSitesF ell M (NcwdhFam.constFam c L) k S ∧ NcwdhFam.CovPlaqF ell M (NcwdhFam.constFam c L) k S ∧
      NcwdhFam.PerCubeRegularF ell M (NcwdhFam.constFam c L) k S α₀ η U) := Iff.rfl
#print axioms probe_nc_imp_cov
#print axioms probe_sep
#print axioms probe_nv
#print axioms probe_cov_imp_sites_hyp
