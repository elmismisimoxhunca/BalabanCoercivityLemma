import Q409W4

/-!
# C5A -- `region_core`: the p.409 stratum/collar core for an ARBITRARY region `P` (not only an `l^1` patch).

`setw_core` (Q409W2) is proved for the `l^1` patch.  Here the same argument is run for any set `P` of sites such that
(hP1) every point of `P` is within `K * G_j` (`l^1`, `G_j = M ell^j`) of an anchor `x0 in B^j`,
(hxP) the anchor is in `P`,
(hsh) `P` contains the anchor shifted by `+-G_j` in every direction (`s = G_j` or `s + G_j = N`).
Conclusion: exactly the data `IsClassSetW`/`IsClassUnion` need (index `i in {j-1, j}`, two strata, meets `B^i`, two level-`i` blocks).
Regime: `K*ell <= R`, `2 <= K`, `2 <= ell`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409C5

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.P409W

variable {L : PeriodicLatticeExtent}

theorem region_core {ell M R k K j : ℕ} {S : Tower L} {x₀ : PeriodicLatticeSite L}
    {P : Set (PeriodicLatticeSite L)}
    (hell : 2 ≤ ell) (hM : 0 < M) (hK : 2 ≤ K) (hR : K * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hjk : j ≤ k) (hx0 : x₀ ∈ towerBj S j)
    (hP1 : ∀ y ∈ P, pdist x₀ y ≤ K * bigSide M ell j)
    (hxP : x₀ ∈ P)
    (hsh : ∀ (μ : Fin 3) (s : ℕ), (s = bigSide M ell j ∨ s + bigSide M ell j = L μ + 1) → sh x₀ μ s ∈ P) :
    ∃ i : ℕ, i ≤ j ∧ bigSide M ell i ∣ bigSide M ell j ∧ bigSide M ell j ≤ ell * bigSide M ell i ∧
      (∀ y ∈ P, y ∈ S.Om 0 → y ∈ towerBj S i ∪ towerBj S (i + 1)) ∧
      (∃ y ∈ P, y ∈ S.Om 0 ∧ y ∈ towerBj S i) ∧
      (∃ a ∈ P, ∃ b ∈ P, a ∈ S.Om 0 ∧ b ∈ S.Om 0 ∧
        ∃ μ : Fin 3, (a μ).val / bigSide M ell i ≠ (b μ).val / bigSide M ell i) := by
  have hell0 : 0 < ell := by omega
  have hx0j : x₀ ∈ S.Om j := hx0.1
  have hx0n : x₀ ∉ S.Om (j + 1) := hx0.2
  set G := bigSide M ell j with hGdef
  have hGpos : 0 < G := bigSide_pos' hM hell0 j
  have hx00 : x₀ ∈ S.Om 0 := AdalyFormal.M1.om_anti hA (Nat.zero_le j) hx0j
  have hRc : K * ell ≤ R := hR
  have hRell : 2 * K ≤ R := by nlinarith
  have hK1' : ∀ y ∈ P, pdist y x₀ ≤ K * G := by
    intro y hy; rw [pdist_comm]; exact hP1 y hy
  -- lower stratum
  have hK2 : ∀ j', j = j' + 1 → ∀ y ∈ P, y ∈ S.Om j' := by
    intro j' hj' y hy
    by_contra hn
    have hx1 : x₀ ∈ S.Om (j' + 1) := hj' ▸ hx0j
    have hcol := AdalyFormal.M1.collar hA (j := j') (by omega) hn hx1
    have hb : G = bigSide M ell j' * ell := by rw [hGdef, hj']; exact AdalyFormal.M1.bigSide_succ M ell j'
    have h1 := hK1' y hy
    have h2 : K * G ≤ R * bigSide M ell j' := by
      rw [hb]
      calc K * (bigSide M ell j' * ell) = (K * ell) * bigSide M ell j' := by ring
        _ ≤ R * bigSide M ell j' := Nat.mul_le_mul_right _ hRc
    omega
  -- the shifted point (levels j >= 1)
  have hshift : 1 ≤ j → ∀ i : ℕ, i ≤ j → bigSide M ell i ∣ G →
      (∃ a ∈ P, ∃ b ∈ P, a ∈ S.Om 0 ∧ b ∈ S.Om 0 ∧
        ∃ μ : Fin 3, (a μ).val / bigSide M ell i ≠ (b μ).val / bigSide M ell i) := by
    intro hj1 i hij hdvd
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hNd : bigSide M ell i ∣ L 0 + 1 := hA.2.2.1 i (by omega) 0
    have hGk : G ≤ bigSide M ell k := bigSide_mono' hell0 hjk
    have hGN : G < L 0 + 1 := lt_of_le_of_lt hGk (hgt 0)
    have hy : sh x₀ 0 G ∈ P := hsh 0 G (Or.inl rfl)
    have hy0 : sh x₀ 0 G ∈ S.Om 0 :=
      AdalyFormal.M1.om_anti hA (Nat.zero_le j') (hK2 j' hj' _ hy)
    refine ⟨x₀, hxP, sh x₀ 0 G, hy, hx00, hy0, 0, ?_⟩
    have hgpos : 0 < bigSide M ell i := bigSide_pos' hM hell0 i
    have := blocks_ne (bigSide M ell i) (L 0 + 1) (x₀ 0).val G hgpos hNd hdvd hGpos hGN (x₀ 0).isLt
    rw [sh_self]
    exact fun h => this h.symm
  by_cases hQ : ∃ y ∈ P, y ∈ S.Om 0 ∧ y ∉ S.Om j
  · -- two strata j-1, j
    obtain ⟨xq, hxq, hxq0, hxqn⟩ := hQ
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := by
      refine ⟨j - 1, ?_⟩
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; exact absurd hxq0 hxqn
      · omega
    have hGi : G = bigSide M ell i * ell := by rw [hGdef, hi]; exact AdalyFormal.M1.bigSide_succ M ell i
    have hgi : 0 < bigSide M ell i := bigSide_pos' hM hell0 i
    have hxqi : xq ∈ S.Om i := hK2 i hi xq hxq
    have hxqn' : xq ∉ S.Om (i + 1) := hi ▸ hxqn
    have hdv : bigSide M ell i ∣ G := by rw [hGi]; exact Dvd.intro _ rfl
    refine ⟨i, by omega, hdv, ?_, ?_, ⟨xq, hxq, hxq0, hxqi, hxqn'⟩, hshift (by omega) i (by omega) hdv⟩
    · rw [hGi]; nlinarith
    · intro y hy hy0
      have hyi : y ∈ S.Om i := hK2 i hi y hy
      have hyn : y ∉ S.Om (i + 2) := by
        intro hy2
        have hcol := AdalyFormal.M1.collar hA (j := i + 1) (by omega) hxqn' (show y ∈ S.Om (i + 1 + 1) from hy2)
        have h1 := pdist_triangle xq x₀ y
        have h2 : pdist x₀ xq ≤ K * G := hP1 xq hxq
        rw [pdist_comm xq x₀] at h1
        have h3 : 2 * K * G ≤ R * G := Nat.mul_le_mul_right _ hRell
        have h4 : bigSide M ell (i + 1) = G := by rw [hGdef, hi]
        rw [h4] at hcol
        have h5 := hP1 y hy
        nlinarith
      by_cases hy1 : y ∈ S.Om (i + 1)
      · exact Or.inr ⟨hy1, hyn⟩
      · exact Or.inl ⟨hyi, hy1⟩
  · push Not at hQ
    have hsub : ∀ y ∈ P, y ∈ S.Om 0 → y ∈ towerBj S j ∪ towerBj S (j + 1) := by
      intro y hy hy0
      have hyj : y ∈ S.Om j := hQ y hy hy0
      have hyn : y ∉ S.Om (j + 2) := by
        intro hy2
        by_cases hjk1 : j + 1 ≤ k
        · have hcol := AdalyFormal.M1.collar hA (j := j + 1) hjk1 hx0n (show y ∈ S.Om (j + 1 + 1) from hy2)
          have h1 := hP1 y hy
          have h4 : bigSide M ell (j + 1) = G * ell := AdalyFormal.M1.bigSide_succ M ell j
          rw [h4] at hcol
          have h5 : K * G ≤ R * (G * ell) := by
            calc K * G ≤ (K * ell) * G := by nlinarith
              _ ≤ R * G := Nat.mul_le_mul_right _ hRc
              _ ≤ R * (G * ell) := Nat.mul_le_mul_left _ (by nlinarith)
          omega
        · rw [hA.2.1 (j + 2) (by omega)] at hy2; exact hy2
      by_cases hy1 : y ∈ S.Om (j + 1)
      · exact Or.inr ⟨hy1, hyn⟩
      · exact Or.inl ⟨hyj, hy1⟩
    by_cases hj0 : j = 0
    · -- j = 0 : a second M-block through the collar clause of Omega_0
      subst hj0
      have hG0 : G = M := bigSide_zero M ell
      have hMk : M ≤ bigSide M ell k := by
        have := bigSide_mono' (M := M) hell0 (Nat.zero_le k)
        rwa [bigSide_zero] at this
      have hNd : ∀ μ : Fin 3, M ∣ L μ + 1 := fun μ => by
        have := hA.2.2.1 0 (Nat.zero_le k) μ; rwa [bigSide_zero] at this
      have hN2 : ∀ μ : Fin 3, 2 * M ≤ L μ + 1 := fun μ => by
        obtain ⟨t, ht⟩ := hNd μ
        have h1 := hgt μ
        have h2 : M < M * t := by omega
        have h3 : 2 ≤ t := by
          by_contra hh; push Not at hh
          interval_cases t <;> omega
        have := Nat.mul_le_mul_left M h3
        omega
      have h6 := (hA.2.2.2.2.2 x₀).1 hx00
      obtain ⟨y₁, hy₁, z, hz, hzd⟩ := h6
      have hRM : 4 ≤ R := by omega
      obtain ⟨μ, s, hs, hzs⟩ := toward_site M R z y₁ hM hRM hN2 hzd
      have hN2μ := hN2 μ
      have hsN : s ≤ L μ + 1 := by omega
      have hMs : M ∣ s := by
        rcases hs with rfl | h
        · exact dvd_rfl
        · have h7 := hNd μ
          have : s = (L μ + 1) - M := by omega
          rw [this]; exact Nat.dvd_sub h7 dvd_rfl
      have hx'0 : sh x₀ μ s ∈ S.Om 0 := by
        refine (hA.2.2.2.2.2 _).2 ⟨y₁, hy₁, sh z μ s, ?_, hzs⟩
        intro ν
        by_cases hν : ν = μ
        · subst hν
          rw [sh_self, sh_self]
          exact div_shift M (L ν + 1) (z ν).val (x₀ ν).val s hM (hNd ν) hMs (hz ν)
        · rw [sh_ne z μ ν s hν, sh_ne x₀ μ ν s hν]; exact hz ν
      have hx'P : sh x₀ μ s ∈ P := by
        refine hsh μ s ?_
        rw [hG0]; exact hs
      have hs0' : 0 < s := by rcases hs with rfl | h <;> omega
      have hsN' : s < L μ + 1 := by
        rcases hs with rfl | h
        · have := hN2 μ; omega
        · omega
      refine ⟨0, le_refl _, dvd_rfl, by nlinarith, hsub, ⟨x₀, hxP, hx00, hx0j, hx0n⟩,
        ⟨x₀, hxP, sh x₀ μ s, hx'P, hx00, hx'0, μ, ?_⟩⟩
      have := blocks_ne (bigSide M ell 0) (L μ + 1) (x₀ μ).val s (bigSide_pos' hM hell0 0)
        (by rw [bigSide_zero]; exact hNd μ) (by rw [bigSide_zero]; exact hMs) hs0' hsN' (x₀ μ).isLt
      rw [sh_self]
      exact fun h => this h.symm
    · exact ⟨j, le_rfl, dvd_rfl, by nlinarith, hsub, ⟨x₀, hxP, hx00, hx0j, hx0n⟩,
        hshift (by omega) j le_rfl dvd_rfl⟩

end AdalyFormal.P409C5
