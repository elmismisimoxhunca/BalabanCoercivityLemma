import SolR6Family
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
namespace SolR6Witness
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2 AdalyFormal.D1Literal AdalyFormal.D1Guarded AdalyFormal.NonVac
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open SolR6Family

theorem utheta_ne_one {θ : ℝ} (hθ : 0 < θ) (hπ : θ < Real.pi) : uθ θ ≠ 1 := by
  intro heq
  have he := congrArg (fun u : SU2m => (((u : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im)) heq
  have hs : Real.sin θ = 0 := by simpa [uθ, uMat, Complex.exp_ofReal_mul_I_im] using he
  have hp := Real.sin_pos_of_pos_of_lt_pi hθ hπ
  rw [hs] at hp
  exact (lt_irrefl 0) hp

theorem outside_bonds {m R : ℕ} (hm : 1 ≤ m) (hR : 18 ≤ R) :
    ∃ e0 e1 : Bond (scaleUp 2 2 (nvLu (2^m) R)),
      e0 ∈ Zb ((SlabNv 2 (2^m) R).Om 0) ∧ e1 ∈ Zb ((SlabNv 2 (2^m) R).Om 0) ∧ e1 ≠ e0 := by
  have hM : 0 < 2^m := pow_pos (by norm_num) m
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2^m) R) μ + 1 = nvN 2 (2^m) R := fun μ => scaleUp_nv (by norm_num) hM μ
  have hN1 : 1 < nvN 2 (2^m) R := by simp only [nvN]; norm_num; nlinarith
  have hP : 2 ≤ nvP0 2 (2^m) R := by simp only [nvP0]; norm_num; nlinarith
  let x : PeriodicLatticeSite (scaleUp 2 2 (nvLu (2^m) R)) := fun μ => ⟨0, Nat.succ_pos _⟩
  have hx : x ∉ (SlabNv 2 (2^m) R).Om 0 := by
    change x ∉ (slab3 _ _ _ _ _ _ _).Om 0
    rw [om0_mem]; change ¬ (_ ≤ 0 ∧ _); omega
  have hx0 : periodicLatticeShift x 0 ∉ (SlabNv 2 (2^m) R).Om 0 := by
    change _ ∉ (slab3 _ _ _ _ _ _ _).Om 0
    rw [om0_mem, shift_val_N hN hN1, if_pos rfl]
    change ¬ (_ ≤ (0+1) % _ ∧ _)
    rw [Nat.mod_eq_of_lt hN1]; omega
  have hx1 : periodicLatticeShift x 1 ∉ (SlabNv 2 (2^m) R).Om 0 := by
    change _ ∉ (slab3 _ _ _ _ _ _ _).Om 0
    rw [om0_mem, adj_shift_coord_N hN hN1 x (show (0 : Fin 3) ≠ 1 by decide)]
    change ¬ (_ ≤ 0 ∧ _); omega
  refine ⟨(x,0), (x,1), ⟨hx,hx0⟩, ⟨hx,hx1⟩, ?_⟩
  intro he; have := congrArg Prod.snd he; norm_num at this

-- Actual NV witness beyond all Uth, with the original smallness/large-scale order.
set_option maxHeartbeats 1000000 in
theorem nv_non_twist_guard :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ α : ℝ, 0 < α → (12 : ℝ) * (2^m : ℕ) * α ≤ a₀ →
      ∃ U : LinkCfg (scaleUp 2 2 (nvLu (2^m) R)),
        TorusOK 2 (2^m) (nvLu (2^m) R) ∧
        Admissible 2 (2^m) R 2 (SlabNv 2 (2^m) R) ∧
        LambdaOK2 2 (2^m) R 2 (SlabNv 2 (2^m) R) (LamN (2^m) R) ∧
        ClassCoupled 2 (2^m) 12 2 (SlabNv 2 (2^m) R) α (((2:ℕ):ℝ)^2)⁻¹ U ∧
        (∀ e : Bond (scaleUp 2 2 (nvLu (2^m) R)), e.1 ∈ (SlabNv 2 (2^m) R).Om 0 → U e = 1) ∧
        IsUnit (dataS selAll selAll (gparams 2 2 (nvLu (2^m) R) (by norm_num) (SlabNv 2 (2^m) R) U 1 (LamN (2^m) R))).Ginv ∧
        (∀ φ : ℝ, U ≠ Uth ((SlabNv 2 (2^m) R).Om 0) φ) := by
  obtain ⟨m₀, hm₀, hmm⟩ := nv_guard_nonvacuous selAll (fun _ _ => Set.subset_univ _)
  refine ⟨m₀, hm₀, fun m hm => ?_⟩
  obtain ⟨R₀, hrr⟩ := hmm m hm
  refine ⟨max R₀ 18, fun R hR => ?_⟩
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨a₀, ha₀, γ, hγ, hall⟩ := hrr R (le_trans (le_max_left _ _) hR)
  refine ⟨a₀, ha₀, fun α hα hsmall => ?_⟩
  obtain ⟨δ0, hδ0, hflat⟩ := hall α hα hsmall
  have hflat0 := hflat 0 (by simpa using hδ0)
  have hM : 0 < 2^m := pow_pos (by norm_num) m
  have hm1 : 1 ≤ m := le_trans hm₀ hm
  have hdvd : 2 ∣ 2^m := dvd_pow_self 2 (by omega)
  have G := slabGeo_inst (ell := 2) (show 2 ≤ 2 by omega) hM hdvd (show 1 ≤ R by omega)
  have hN : ∀ μ, scaleUp 2 2 (nvLu (2^m) R) μ + 1 = nvN 2 (2^m) R := fun μ => scaleUp_nv (by norm_num) hM μ
  have hAdm : Admissible 2 (2^m) R 2 (SlabNv 2 (2^m) R) := slab3_admissible G hN
  have hroom : 17*2 ≤ R * 2^m := by
    have hM2 : 2 ≤ 2^m := by
      calc 2 = 2^1 := by norm_num
           _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm1
    nlinarith
  obtain ⟨e0,e1,hz0,hz1,hne⟩ := outside_bonds hm1 hR18
  have eU : sparse e0 0 = Uth ((SlabNv 2 (2^m) R).Om 0) 0 :=
    (sparse_zero e0).trans (Uth_zero _).symm
  have hu0 : IsUnit (sparseF (S := SlabNv 2 (2^m) R) (by norm_num) 1 (LamN (2^m) R) e0 selAll 0) := by
    change IsUnit (dataS selAll selAll (gparams 2 2 (nvLu (2^m) R) (by norm_num) (SlabNv 2 (2^m) R) (sparse e0 0) 1 (LamN (2^m) R))).Ginv
    rw [eU]
    exact hflat0.2.1
  obtain ⟨δ,hδ,hunits⟩ := sparse_guard_near_zero (by norm_num) hAdm (by norm_num) hroom 1 (LamN (2^m) R) e0 hz0 selAll hu0
  let θ := min δ Real.pi / 2
  have hθ : 0 < θ := by dsimp [θ]; exact div_pos (lt_min hδ Real.pi_pos) (by norm_num)
  have hθδ : |θ| < δ := by rw [abs_of_pos hθ]; dsimp [θ]; have := min_le_left δ Real.pi; linarith [lt_min hδ Real.pi_pos]
  have hθπ : θ < Real.pi := by dsimp [θ]; have := min_le_right δ Real.pi; linarith [lt_min hδ Real.pi_pos]
  refine ⟨sparse e0 θ, torusOK_nv (by norm_num) hdvd hM, hAdm,
    lambdaOK2_nv (by norm_num) hdvd hM (show 1 ≤ R by omega), ?_, sparse_base e0 hz0 θ, hunits θ hθδ, ?_⟩
  · exact sparse_class hAdm.1 hflat0.1.1 hα hM (by norm_num) (by norm_num) (by positivity) e0 hz0 θ
  · exact sparse_not_twist e0 e1 hz0 hz1 hne θ (utheta_ne_one hθ hθπ)
#print axioms outside_bonds
#print axioms nv_non_twist_guard
end SolR6Witness
