import W6C

/-!
# W6D -- the size of the multi-level flat right inverse (W6 lane, 2026-10-13)

`wF p = (ℓ^{lev p})³` (the row normalisation: a flat level-`j` row has norm `~ ℓ^{-3j/2}`), `‖y‖_F² = Σ_p wF p ‖y_p‖²`.
* `Elev j y` : the level-`j` part `Σ_{rows b of level j} phiK (j,b) • y_(j,b)`; it is `gbondE tprof pprof n Wlo + gbondE uprof pprof n Wup`
  (`Elev_eq`), with coarse-bond data `Wlo`, `Wup` of total mass `Σ_b ‖y_(j,b)‖²` (`W_mass`).
* `EflatL_split` : `‖E y‖² = Σ_j ‖Elev j y‖²` (kernels of different levels sit on different strata, `phi_strat`).
* **`EflatL_norm_sq`** : `‖E y‖² ≤ CE · ‖y‖_F²`, `CE = 2·(410.0625 + 5513.0625) = 11846.25`, free of `k`, `ℓ`, `M`, `R`, the
  volume and the tower.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.W6P (gbK gbondE tprof pprof SProf sprof_tprof sprof_pprof gbondE_norm_sq)

/-- a square-sum with at most one nonzero term -/
theorem norm_sq_sum_single {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] (g : ι → V)
    (h : ∀ a a', g a ≠ 0 → g a' ≠ 0 → a = a') : ‖∑ a, g a‖ ^ 2 = ∑ a, ‖g a‖ ^ 2 := by
  classical
  by_cases hex : ∃ a, g a ≠ 0
  · obtain ⟨a, ha⟩ := hex
    have h1 : ∑ a', g a' = g a := Finset.sum_eq_single a (fun b _ hb => by
      by_contra hne; exact hb (h b a hne ha)) (fun hh => absurd (mem_univ a) hh)
    have h2 : ∑ a', ‖g a'‖ ^ 2 = ‖g a‖ ^ 2 := Finset.sum_eq_single a (fun b _ hb => by
      by_contra hne
      have : g b ≠ 0 := by intro h0; apply hne; rw [h0, norm_zero]; ring
      exact hb (h b a this ha)) (fun hh => absurd (mem_univ a) hh)
    rw [h1, h2]
  · push_neg at hex
    simp [hex]

section norm
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- the rows of one level form a finite type (the same classical instance as the one behind `BIdx`) -/
noncomputable instance fiberFintype (j : ℕ) : Fintype {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j} := by
  classical
  exact inferInstance

/-- the row weight `(ℓ^j)³` -/
noncomputable def wF (p : BIdx (geomOf ell k S)) : ℝ := ((ell : ℝ) ^ (p.1 : ℕ)) ^ 3

theorem wF_pos (hell : 0 < ell) (p : BIdx (geomOf ell k S)) : 0 < wF p := by
  unfold wF; have : (0 : ℝ) < ell := by exact_mod_cast hell
  positivity

/-- the weighted square norm on `L²(𝔅)` -/
noncomputable def nF (y : FSp (geomOf ell k S)) : ℝ := ∑ p, wF p * ‖y p‖ ^ 2

theorem nF_nonneg (hell : 0 < ell) (y : FSp (geomOf ell k S)) : 0 ≤ nF y :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (wF_pos hell p).le (sq_nonneg _))

/-- the level-`j` part of `E y` -/
noncomputable def Elev (hell : 0 < ell) (j : Fin (k + 1)) (y : FSp (geomOf ell k S)) (b : Bond (scaleUp ell k Lu)) : SuTwo :=
  ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, phiK hell ⟨j, r⟩ b • y ⟨j, r⟩

open Classical in
/-- the lower entry of row `r` at the coarse bond `c` -/
noncomputable def Flo (hell : 0 < ell) (j : Fin (k + 1)) (y : FSp (geomOf ell k S))
    (r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j})
    (c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ))) : SuTwo :=
  if ¬ useUp (⟨j, r⟩ : BIdx (geomOf ell k S)) ∧ rowCB hell ⟨j, r⟩ = c then y ⟨j, r⟩ else 0

open Classical in
/-- the upper entry of row `r` at the coarse bond `c` -/
noncomputable def Fup (hell : 0 < ell) (j : Fin (k + 1)) (y : FSp (geomOf ell k S))
    (r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j})
    (c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ))) : SuTwo :=
  if useUp (⟨j, r⟩ : BIdx (geomOf ell k S)) ∧ cbUp (ell ^ (j : ℕ)) (hdvdL hell ⟨j, r⟩) (rowCB hell ⟨j, r⟩) = c
  then y ⟨j, r⟩ else 0

/-- lower data at level `j` -/
noncomputable def Wlo (hell : 0 < ell) (j : Fin (k + 1)) (y : FSp (geomOf ell k S))
    (c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ))) : SuTwo :=
  ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, Flo hell j y r c

/-- upper data at level `j` -/
noncomputable def Wup (hell : 0 < ell) (j : Fin (k + 1)) (y : FSp (geomOf ell k S))
    (c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ))) : SuTwo :=
  ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, Fup hell j y r c

/-- a row as a coarse bond of its level -/
def rowCBj (hell : 0 < ell) (j : Fin (k + 1)) (r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}) :
    CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ)) := rowCB hell ⟨j, r⟩

open Classical in
theorem Elev_eq (hell : 0 < ell) (j : Fin (k + 1)) (y : FSp (geomOf ell k S)) (b : Bond (scaleUp ell k Lu)) :
    Elev hell j y b = gbondE (tprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) (Wlo hell j y) b
      + gbondE (AdalyFormal.W6.uprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) (Wup hell j y) b := by
  simp only [Elev, gbondE, Wlo, Wup, Finset.smul_sum]
  rw [Finset.sum_comm (s := (univ : Finset (CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ))))),
    Finset.sum_comm (s := (univ : Finset (CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ))))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [Flo, Fup]
  unfold phiK
  by_cases hu : useUp (⟨j, r⟩ : BIdx (geomOf ell k S))
  · rw [if_pos hu]
    have hlo : ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ)),
        gbK (tprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) b.1 b.2 c •
          (if ¬ useUp (⟨j, r⟩ : BIdx (geomOf ell k S)) ∧ rowCB hell ⟨j, r⟩ = c then y ⟨j, r⟩ else 0) = 0 :=
      Finset.sum_eq_zero (fun c _ => by rw [if_neg (fun h => h.1 hu), smul_zero])
    rw [hlo, zero_add]
    rw [Finset.sum_eq_single (cbUp (ell ^ (j : ℕ)) (hdvdL hell ⟨j, r⟩) (rowCB hell ⟨j, r⟩))]
    · rw [if_pos ⟨hu, rfl⟩]
    · intro c _ hc
      rw [if_neg (fun h => hc h.2.symm), smul_zero]
    · intro h; exact absurd (mem_univ _) h
  · rw [if_neg hu]
    have hup : ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ)),
        gbK (AdalyFormal.W6.uprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) b.1 b.2 c •
          (if useUp (⟨j, r⟩ : BIdx (geomOf ell k S)) ∧
            cbUp (ell ^ (j : ℕ)) (hdvdL hell ⟨j, r⟩) (rowCB hell ⟨j, r⟩) = c then y ⟨j, r⟩ else 0) = 0 :=
      Finset.sum_eq_zero (fun c _ => by rw [if_neg (fun h => hu h.1), smul_zero])
    rw [hup, add_zero]
    rw [Finset.sum_eq_single (rowCB hell ⟨j, r⟩)]
    · rw [if_pos ⟨hu, rfl⟩]
    · intro c _ hc
      rw [if_neg (fun h => hc h.2.symm), smul_zero]
    · intro h; exact absurd (mem_univ _) h

theorem rowCBj_inj (hell : 0 < ell) (j : Fin (k + 1)) :
    Function.Injective (rowCBj (S := S) hell j) := by
  intro r r' h
  have h1 := congrArg (fun c => c.1.1) h
  have h2 := congrArg (fun c => c.2) h
  simp only [rowCBj, rowCB] at h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

/-- the square mass of the coarse data of one kind at one level -/
theorem mass_kind {α β V : Type*} [Fintype α] [Fintype β] [NormedAddCommGroup V] (F : α → β → V) (f : α → β)
    (hf : Function.Injective f) (hsupp : ∀ a c, F a c ≠ 0 → f a = c) :
    ∑ c, ‖∑ a, F a c‖ ^ 2 = ∑ a, ‖F a (f a)‖ ^ 2 := by
  have h1 : ∀ c, ‖∑ a, F a c‖ ^ 2 = ∑ a, ‖F a c‖ ^ 2 := by
    intro c
    apply norm_sq_sum_single
    intro a a' ha ha'
    exact hf ((hsupp a c ha).trans (hsupp a' c ha').symm)
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single (f a)]
  · intro c _ hc
    by_contra hne
    have : F a c ≠ 0 := by intro h0; apply hne; rw [h0, norm_zero]; ring
    exact hc (hsupp a c this).symm
  · intro h; exact absurd (mem_univ _) h

theorem W_mass (hell : 0 < ell) (j : Fin (k + 1)) (y : FSp (geomOf ell k S)) :
    ∑ c, ‖Wlo hell j y c‖ ^ 2 + ∑ c, ‖Wup hell j y c‖ ^ 2
      = ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ‖y ⟨j, r⟩‖ ^ 2 := by
  have hlo := mass_kind (Flo hell j y) (rowCBj hell j) (rowCBj_inj hell j) (fun r c h => by
    unfold Flo at h
    by_contra hne; exact h (if_neg (fun hh => hne hh.2)))
  have hup := mass_kind (Fup hell j y)
      (fun r => cbUp (ell ^ (j : ℕ)) (hdvdL hell ⟨j, r⟩) (rowCBj hell j r))
      (fun r r' h => rowCBj_inj hell j (cbUp_inj _ h)) (fun r c h => by
        unfold Fup at h
        by_contra hne; exact h (if_neg (fun hh => hne hh.2)))
  simp only [Wlo, Wup]
  rw [hlo, hup, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [Flo, Fup, rowCBj]
  by_cases hu : useUp (⟨j, r⟩ : BIdx (geomOf ell k S))
  · rw [if_neg (fun hh => hh.1 hu), if_pos ⟨hu, rfl⟩, norm_zero]; ring
  · rw [if_pos ⟨hu, rfl⟩, if_neg (fun hh => hu hh.1), norm_zero]; ring

/-- level parts as a sum over levels -/
theorem EflatL_eq_sum (hell : 0 < ell) (y : FSp (geomOf ell k S)) (b : Bond (scaleUp ell k Lu)) :
    (EflatL hell y) b = ∑ j : Fin (k + 1), Elev hell j y b := by
  rw [EflatL_apply]
  unfold Elev
  exact Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => phiK hell p b • y p)

/-- a nonzero level part sits on a bond based at a site of that stratum -/
theorem Elev_lev (hell : 0 < ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S)) (b : Bond (scaleUp ell k Lu))
    (i : Fin (k + 1)) (hi : Elev hell i y b ≠ 0) : AdalyFormal.M1.strat S k b.1 = (i : ℕ) := by
  unfold Elev at hi
  obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hphi : phiK hell ⟨i, r⟩ b ≠ 0 := by
    intro h0; apply hr; rw [h0, zero_smul]
  exact phi_strat hell hS ⟨i, r⟩ b hphi

/-- pointwise: `‖E y (b)‖² = Σ_j ‖E_j y (b)‖²` -/
theorem EflatL_pt (hell : 0 < ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S)) (b : Bond (scaleUp ell k Lu)) :
    ‖(EflatL hell y) b‖ ^ 2 = ∑ j : Fin (k + 1), ‖Elev hell j y b‖ ^ 2 := by
  rw [show (EflatL hell y) b = ∑ j : Fin (k + 1), Elev hell j y b from EflatL_eq_sum hell y b]
  apply norm_sq_sum_single
  intro j j' hj hj'
  exact Fin.ext ((Elev_lev hell hS y b j hj).symm.trans (Elev_lev hell hS y b j' hj'))

/-- **`‖E y‖² = Σ_j ‖E_j y‖²`** (different levels on different strata) -/
theorem EflatL_split (hell : 0 < ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S)) :
    ‖EflatL hell y‖ ^ 2 = ∑ j : Fin (k + 1), ∑ b, ‖Elev hell j y b‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [show (EflatL hell y) b = ∑ j : Fin (k + 1), Elev hell j y b from EflatL_eq_sum hell y b]
  apply norm_sq_sum_single
  intro j j' hj hj'
  have hlev : ∀ i : Fin (k + 1), Elev hell i y b ≠ 0 → AdalyFormal.M1.strat S k b.1 = (i : ℕ) := by
    intro i hi
    unfold Elev at hi
    obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    have hphi : phiK hell ⟨i, r⟩ b ≠ 0 := by
      intro h0; apply hr; rw [h0, zero_smul]
    exact phi_strat hell hS ⟨i, r⟩ b hphi
  exact Fin.ext ((hlev j hj).symm.trans (hlev j' hj'))

theorem norm_add_sq_le2 {V : Type*} [NormedAddCommGroup V] (u v : V) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_add_le u v
  have h0 := norm_nonneg (u + v)
  nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]

theorem comb_le (A B X Y n3 : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hn : 0 ≤ n3) :
    2 * (A * n3 * X) + 2 * (B * n3 * Y) ≤ 2 * (A + B) * (n3 * (X + Y)) := by
  nlinarith [mul_nonneg (mul_nonneg hA hn) hY, mul_nonneg (mul_nonneg hB hn) hX]

/-- the norm constant of `E` -/
noncomputable def CE : ℝ := 2 * ((9 * (3 / 2) ^ 2) ^ 2 + (33 * (3 / 2) ^ 2) ^ 2)

/-- **one level: `Σ_b ‖E_j y (b)‖² ≤ CE ℓ^{3j} Σ_{rows of level j} ‖y_r‖²`** -/
theorem Elev_norm_sq (hell : 0 < ell) (hell2 : 2 ≤ ell) (y : FSp (geomOf ell k S)) (j : Fin (k + 1)) :
    ∑ b, ‖Elev hell j y b‖ ^ 2
      ≤ CE * ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
          wF (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖y ⟨j, r⟩‖ ^ 2 := by
  have hn : 0 < ell ^ (j : ℕ) := pow_pos hell _
  have hdv : ∀ ν, ell ^ (j : ℕ) ∣ scaleUp ell k Lu ν + 1 :=
    fun ν => AdalyFormal.BondComposite.hdvd_scaleUp ell k Lu hell _ (Nat.lt_succ_iff.mp j.isLt) ν
  set n : ℝ := ((ell ^ (j : ℕ) : ℕ) : ℝ) with hndef
  have hwF : ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
      wF (⟨j, r⟩ : BIdx (geomOf ell k S)) = n ^ 3 := by
    intro r; unfold wF; rw [hndef]; push_cast; rfl
  simp only [hwF]
  rw [← Finset.mul_sum]
  have hlo := gbondE_norm_sq (sprof_tprof _ hn) (sprof_pprof _ hn) hdv (Wlo hell j y)
  have hsplit : ∀ b, ‖Elev hell j y b‖ ^ 2
      ≤ 2 * ‖gbondE (tprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) (Wlo hell j y) b‖ ^ 2
        + 2 * ‖gbondE (AdalyFormal.W6.uprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ))
            (Wup hell j y) b‖ ^ 2 := by
    intro b
    rw [Elev_eq]
    exact norm_add_sq_le2 _ _
  -- the upper part
  have hup : ∑ b, ‖gbondE (AdalyFormal.W6.uprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ))
      (Wup hell j y) b‖ ^ 2 ≤ (33 * (3 / 2) ^ 2) ^ 2 * n ^ 3 * ∑ c, ‖Wup hell j y c‖ ^ 2 := by
    by_cases hj0 : (j : ℕ) = 0
    · -- no upper rows at level 0
      have hW : ∀ c, Wup hell j y c = 0 := by
        intro c
        unfold Wup
        refine Finset.sum_eq_zero (fun r _ => ?_)
        unfold Fup
        rw [if_neg]
        rintro ⟨hu, -⟩
        have := hu.1
        simp only at this
        omega
      have h0 : ∀ b, gbondE (AdalyFormal.W6.uprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ))
          (Wup hell j y) b = 0 := by
        intro b; unfold gbondE; simp [hW]
      simp only [h0, hW, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
        mul_zero, le_refl]
    · have hn2 : 2 ≤ ell ^ (j : ℕ) := le_trans hell2 (by
        calc ell = ell ^ 1 := (pow_one ell).symm
          _ ≤ ell ^ (j : ℕ) := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hj0))
      exact gbondE_norm_sq (AdalyFormal.W6.sprof_uprof _ hn2) (sprof_pprof _ hn) hdv (Wup hell j y)
  have hmass := W_mass hell j y
  have hsum : ∑ b, ‖Elev hell j y b‖ ^ 2
      ≤ 2 * ((9 * (3 / 2) ^ 2) ^ 2 * n ^ 3 * ∑ c, ‖Wlo hell j y c‖ ^ 2)
        + 2 * ((33 * (3 / 2) ^ 2) ^ 2 * n ^ 3 * ∑ c, ‖Wup hell j y c‖ ^ 2) := by
    refine (Finset.sum_le_sum (fun b _ => hsplit b)).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hlo' : ∑ b, ‖gbondE (tprof (ell ^ (j : ℕ))) (pprof (ell ^ (j : ℕ))) (ell ^ (j : ℕ)) (Wlo hell j y) b‖ ^ 2
        ≤ (9 * (3 / 2) ^ 2) ^ 2 * n ^ 3 * ∑ c, ‖Wlo hell j y c‖ ^ 2 := hlo
    linarith
  have hA : 0 ≤ ∑ c, ‖Wlo hell j y c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ ∑ c, ‖Wup hell j y c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn3 : 0 ≤ n ^ 3 := by positivity
  unfold CE
  calc ∑ b, ‖Elev hell j y b‖ ^ 2
      ≤ 2 * ((9 * (3 / 2) ^ 2) ^ 2 * n ^ 3 * ∑ c, ‖Wlo hell j y c‖ ^ 2)
        + 2 * ((33 * (3 / 2) ^ 2) ^ 2 * n ^ 3 * ∑ c, ‖Wup hell j y c‖ ^ 2) := hsum
    _ ≤ 2 * ((9 * (3 / 2) ^ 2) ^ 2 + (33 * (3 / 2) ^ 2) ^ 2) * (n ^ 3 *
          (∑ c, ‖Wlo hell j y c‖ ^ 2 + ∑ c, ‖Wup hell j y c‖ ^ 2)) :=
        comb_le _ _ _ _ _ (by norm_num) (by norm_num) hA hB hn3
    _ = 2 * ((9 * (3 / 2) ^ 2) ^ 2 + (33 * (3 / 2) ^ 2) ^ 2) * (n ^ 3 *
          ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ‖y ⟨j, r⟩‖ ^ 2) := by rw [hmass]

/-- **`‖E y‖² ≤ CE ‖y‖_F²`** -/
theorem EflatL_norm_sq (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (y : FSp (geomOf ell k S)) :
    ‖EflatL hell y‖ ^ 2 ≤ CE * nF y := by
  rw [EflatL_split hell hS y]
  unfold nF
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wF p * ‖y p‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => Elev_norm_sq hell hell2 y j)

end norm

end AdalyFormal.W6

#print axioms AdalyFormal.W6.norm_sq_sum_single
#print axioms AdalyFormal.W6.mass_kind
#print axioms AdalyFormal.W6.fiberFintype
#print axioms AdalyFormal.W6.wF
#print axioms AdalyFormal.W6.wF_pos
#print axioms AdalyFormal.W6.nF
#print axioms AdalyFormal.W6.nF_nonneg
#print axioms AdalyFormal.W6.Elev
#print axioms AdalyFormal.W6.Flo
#print axioms AdalyFormal.W6.Fup
#print axioms AdalyFormal.W6.Wlo
#print axioms AdalyFormal.W6.rowCBj
#print axioms AdalyFormal.W6.Wup
#print axioms AdalyFormal.W6.Elev_eq
#print axioms AdalyFormal.W6.rowCBj_inj
#print axioms AdalyFormal.W6.norm_add_sq_le2
#print axioms AdalyFormal.W6.comb_le
#print axioms AdalyFormal.W6.W_mass
#print axioms AdalyFormal.W6.EflatL_eq_sum
#print axioms AdalyFormal.W6.Elev_lev
#print axioms AdalyFormal.W6.EflatL_pt
#print axioms AdalyFormal.W6.EflatL_split
#print axioms AdalyFormal.W6.Elev_norm_sq
#print axioms AdalyFormal.W6.CE
#print axioms AdalyFormal.W6.EflatL_norm_sq
