import TL1l

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2

theorem bigSide_pos {L : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S)
    {j : ℕ} (hj : j ≤ k) : 0 < bigSide M ell j :=
  Nat.pos_of_dvd_of_pos (hS.2.2.1 j hj 0) (Nat.succ_pos _)

theorem liftTower_mono {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {S : Tower L}
    (hm : ∀ j, S.Om (j + 1) ⊆ S.Om j) : ∀ j, (liftTower h S).Om (j + 1) ⊆ (liftTower h S).Om j :=
  fun j _ hx => hm j hx

theorem coversSites_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R c k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hc : 2 ≤ c)
    (hCov : CoversOm0c ell M c k S) : CoversOm0c ell M c k (liftTower h S) := by
  intro x hx
  obtain ⟨C, j, hC, hxC⟩ := hCov (projS h x) hx
  obtain ⟨hj, ⟨z, hgrid, rfl⟩, -, -⟩ := hC.1
  have hb := bigSide_pos hS hj
  have hbs : bigSide M ell j < c * bigSide M ell j := by nlinarith
  obtain ⟨zt, hgt, hcomp, hper⟩ := corner_site h hstrict (bigSide M ell j) (c * bigSide M ell j) hb hbs
    (fun μ => hS.2.2.1 j hj μ) z hgrid x (fun _ => 0) (fun μ => hxC μ) (fun μ hp => by simp at hp)
  have hdesc := described_lift h hC.1 hgt hcomp
  exact ⟨siteBox zt (c * bigSide M ell j), j,
    isClassCube_of_described (S := liftTower h S) (liftTower_mono h hS.1) hdesc, fun μ => (hper μ).1⟩

theorem inBox_shift {L : PeriodicLatticeExtent} {z : PeriodicLatticeSite L} {s : ℕ} {y : PeriodicLatticeSite L}
    (hy : ∀ ρ : Fin 3, off (L ρ + 1) (z ρ).val (y ρ).val < s) (μ : Fin 3)
    (hμ : off (L μ + 1) (z μ).val (((y μ).val + 1) % (L μ + 1)) < s) :
    ∀ ρ : Fin 3, off (L ρ + 1) (z ρ).val ((periodicLatticeShift y μ) ρ).val < s := by
  intro ρ
  by_cases hρ : ρ = μ
  · subst hρ
    simp only [periodicLatticeShift, Function.update_self, fin_add_one_val]
    exact hμ
  · simp only [periodicLatticeShift, Function.update_of_ne hρ]
    exact hy ρ

theorem edge_mem' {L : PeriodicLatticeExtent} (p : PeriodicLatticePlaquette L) (e : PeriodicLatticeEdge L) :
    e ∈ periodicPlaquetteBoundaryEdges p ↔
      (e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
        e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2)) := by
  simp [periodicPlaquetteBoundaryEdges]

theorem cubeBond_om_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {S : Tower L} {e : PeriodicLatticeEdge Lt}
    (he : CubeBond ((liftTower h S).Om 0) e) : CubeBond (S.Om 0) (projE h e) := by
  refine ⟨he.1, ?_⟩
  have := he.2
  show periodicLatticeShift (projS h e.1) e.2 ∈ S.Om 0
  rw [← projS_shift]; exact this

theorem coversPlaq_lift {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (hstrict : ∀ μ : Fin 3, L μ + 1 < Lt μ + 1)
    {ell M R c k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hc : 2 ≤ c)
    (hCov : CoversPlaqOm0c ell M c k S) : CoversPlaqOm0c ell M c k (liftTower h S) := by
  intro pt hpt
  obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := pt
  let p : PeriodicLatticePlaquette L := (projS h x, ⟨(μ, ν), hμν⟩)
  have hbd : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e := by
    intro e he
    rw [edge_mem'] at he
    have m1 := cubeBond_om_lift h (hpt (x, μ) ((edge_mem' _ _).mpr (Or.inl rfl)))
    have m2 := cubeBond_om_lift h (hpt (periodicLatticeShift x μ, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inl rfl))))
    have m3 := cubeBond_om_lift h (hpt (periodicLatticeShift x ν, μ) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))))
    have m4 := cubeBond_om_lift h (hpt (x, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr rfl)))))
    simp only [projE, projS_shift] at m1 m2 m3 m4
    rcases he with rfl | rfl | rfl | rfl
    · exact m1
    · exact m2
    · exact m3
    · exact m4
  obtain ⟨C, j, hC, hall⟩ := hCov p hbd
  obtain ⟨hj, ⟨z, hgrid, rfl⟩, -, -⟩ := hC.1
  have hb := bigSide_pos hS hj
  have hbs : bigSide M ell j < c * bigSide M ell j := by nlinarith
  have hne : ν ≠ μ := ne_of_gt hμν
  have c1 := hall (projS h x, μ) ((edge_mem' _ _).mpr (Or.inl rfl))
  have c4 := hall (projS h x, ν) ((edge_mem' _ _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have proj_succ : ∀ ρ : Fin 3, ((projS h x ρ).val + 1) % (L ρ + 1) = ((x ρ).val + 1) % (L ρ + 1) := by
    intro ρ; simp only [projS_val]; rw [Nat.mod_add_mod]
  obtain ⟨zt, hgt, hcomp, hper⟩ := corner_site h hstrict (bigSide M ell j) (c * bigSide M ell j) hb hbs
    (fun ρ => hS.2.2.1 j hj ρ) z hgrid x (fun ρ => if ρ = μ ∨ ρ = ν then 1 else 0)
    (fun ρ => c1.1 ρ) (fun ρ hρ => by
      by_cases h1 : ρ = μ
      · subst h1
        have := c1.2 ρ
        simp only [periodicLatticeShift, Function.update_self, fin_add_one_val] at this
        rw [← proj_succ]; exact this
      · have h2 : ρ = ν := by
          by_contra h2; simp [h1, h2] at hρ
        subst h2
        have := c4.2 ρ
        simp only [periodicLatticeShift, Function.update_self, fin_add_one_val] at this
        rw [← proj_succ]; exact this)
  have hdesc := described_lift h hC.1 hgt hcomp
  refine ⟨siteBox zt (c * bigSide M ell j), j,
    isClassCube_of_described (S := liftTower h S) (liftTower_mono h hS.1) hdesc, ?_⟩
  have hb0 : ∀ ρ : Fin 3, off (Lt ρ + 1) (zt ρ).val (x ρ).val < c * bigSide M ell j := fun ρ => (hper ρ).1
  have hflag : ∀ ρ : Fin 3, (ρ = μ ∨ ρ = ν) → off (Lt ρ + 1) (zt ρ).val (((x ρ).val + 1) % (Lt ρ + 1)) < c * bigSide M ell j :=
    fun ρ hρ => (hper ρ).2 (by simp [hρ])
  have hbm := inBox_shift hb0 μ (hflag μ (Or.inl rfl))
  have hbn := inBox_shift hb0 ν (hflag ν (Or.inr rfl))
  have hbmn := inBox_shift hbm ν (by
    have : (periodicLatticeShift x μ) ν = x ν := by simp [periodicLatticeShift, Function.update_of_ne hne]
    rw [this]; exact hflag ν (Or.inr rfl))
  have hbnm := inBox_shift hbn μ (by
    have : (periodicLatticeShift x ν) μ = x μ := by simp [periodicLatticeShift, Function.update_of_ne hne.symm]
    rw [this]; exact hflag μ (Or.inl rfl))
  intro e he
  rw [edge_mem'] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hb0, hbm⟩
  · exact ⟨hbm, hbmn⟩
  · exact ⟨hbn, hbnm⟩
  · exact ⟨hb0, hbn⟩

end AdalyFormal.Thin
