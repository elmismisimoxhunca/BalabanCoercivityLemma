import DLR92

/-!
# DL93 -- continuity of the explicit CT constants `FF.*` (limits along any filter)

For parameter functions `c δD δQ m q cG : X → ℝ` converging along a filter `L` to `(c₀, δD₀, δQ₀, m₀, q₀, cG₀)` with `c₀ > 0` and
`cG₀ ≠ 0`, every `FF.*` constant of the site / `Γ` / `G⁻¹` level converges to its value at the limit parameters; at the Schur level
(`FF.X0 … FF.EN`) the same holds for any limits of the `G⁻¹`-level inputs with `cg₀ ≠ 0`.  (No numerics; the degenerate-point
values are evaluated in DL94.)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open Filter Topology

theorem tdiv {X : Type*} {L : Filter X} {f g : X → ℝ} {a b : ℝ} (hf : Tendsto f L (𝓝 a)) (hg : Tendsto g L (𝓝 b))
    (hb : b ≠ 0) : Tendsto (fun x => f x / g x) L (𝓝 (a / b)) := hf.div hg hb

theorem tcdiv {X : Type*} {L : Filter X} {g : X → ℝ} {b : ℝ} (k : ℝ) (hg : Tendsto g L (𝓝 b)) (hb : b ≠ 0) :
    Tendsto (fun x => k / g x) L (𝓝 (k / b)) := tendsto_const_nhds.div hg hb

namespace FFlim

variable {X : Type*} {L : Filter X} {c δD δQ m q cG : X → ℝ} {c₀ δD₀ δQ₀ m₀ q₀ cG₀ : ℝ}
  (hc : Tendsto c L (𝓝 c₀)) (hc₀ : 0 < c₀) (hD : Tendsto δD L (𝓝 δD₀)) (hQ : Tendsto δQ L (𝓝 δQ₀))
  (hm : Tendsto m L (𝓝 m₀)) (hq : Tendsto q L (𝓝 q₀)) (hG : Tendsto cG L (𝓝 cG₀)) (hG₀ : cG₀ ≠ 0)

include hc hc₀ in
theorem tsq : Tendsto (fun x => Real.sqrt (c x)) L (𝓝 (Real.sqrt c₀)) := hc.sqrt

include hc₀ in
theorem sq0 : Real.sqrt c₀ ≠ 0 := (Real.sqrt_pos.mpr hc₀).ne'

include hc hc₀ hD hQ hm hq in
theorem tK0 : Tendsto (fun x => FF.K0 (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.K0 c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.K0
  exact (((tcdiv 48 hc hc₀.ne').sqrt.mul hD).add ((tcdiv 8 hc hc₀.ne').mul (hD.pow 2))).add
    (((tcdiv 4 hc hc₀.ne').mul hm).mul (((tendsto_const_nhds.mul hq).mul hQ).add (hQ.pow 2)))

include hc hc₀ hD hQ hm hq in
theorem tK1 : Tendsto (fun x => FF.K1 (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.K1 c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.K1
  exact ((tendsto_const_nhds.mul hD).add ((tendsto_const_nhds.mul (tcdiv 12 hc hc₀.ne').sqrt).mul (hD.pow 2))).add
    (((tcdiv 12 hc hc₀.ne').sqrt.mul hm).mul (((tendsto_const_nhds.mul hq).mul hQ).add (hQ.pow 2)))

include hc hc₀ hD hQ hm hq in
theorem tepsX : Tendsto (fun x => FF.epsX (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.epsX c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.epsX
  exact (((tcdiv 4 hc hc₀.ne').mul hQ).add (((tcdiv 4 hc hc₀.ne').mul hD).mul (tdiv hq (tsq hc hc₀) (sq0 hc₀)))).add
    ((tK0 hc hc₀ hD hQ hm hq).mul (tdiv hq hc hc₀.ne'))

include hc hc₀ hD hQ hm hq in
theorem tepsDX : Tendsto (fun x => FF.epsDX (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.epsDX c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.epsDX
  exact (((tcdiv 12 hc hc₀.ne').sqrt.mul hQ).add (((tcdiv 12 hc hc₀.ne').sqrt.mul hD).mul
    (tdiv hq (tsq hc hc₀) (sq0 hc₀)))).add ((tK1 hc hc₀ hD hQ hm hq).mul (tdiv hq hc hc₀.ne'))

include hc hc₀ hD hQ hm hq in
theorem tdGam : Tendsto (fun x => FF.dGam (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.dGam c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.dGam
  exact ((tendsto_const_nhds.mul (tepsX hc hc₀ hD hQ hm hq)).mul (tdiv hq hc hc₀.ne')).add ((tepsX hc hc₀ hD hQ hm hq).pow 2)

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tdGi : Tendsto (fun x => FF.dGi (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.dGi c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.dGi
  exact tdiv (tdGam hc hc₀ hD hQ hm hq) (hG.pow 2) (pow_ne_zero 2 hG₀)

include hc hc₀ hD hQ hm hq in
theorem tnX : Tendsto (fun x => FF.nX (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.nX c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.nX
  exact (tdiv hq hc hc₀.ne').add (tepsX hc hc₀ hD hQ hm hq)

include hc hc₀ hD hQ hm hq in
theorem tnDX : Tendsto (fun x => FF.nDX (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.nDX c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.nDX
  exact (tdiv hq (tsq hc hc₀) (sq0 hc₀)).add (tepsDX hc hc₀ hD hQ hm hq)

include hc hc₀ hD hQ hm hq in
theorem tkF : Tendsto (fun x => FF.kF (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.kF c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.kF
  exact (tnDX hc hc₀ hD hQ hm hq).add (hD.mul (tnX hc hc₀ hD hQ hm hq))

include hc hc₀ hD hQ hm hq in
theorem tdF : Tendsto (fun x => FF.dF (c x) (δD x) (δQ x) (m x) (q x)) L (𝓝 (FF.dF c₀ δD₀ δQ₀ m₀ q₀)) := by
  unfold FF.dF
  exact (hD.mul (tnX hc hc₀ hD hQ hm hq)).add (tepsDX hc hc₀ hD hQ hm hq)

include hG hG₀ in
theorem tgi : Tendsto (fun x => FF.gi (cG x)) L (𝓝 (FF.gi cG₀)) := by
  unfold FF.gi
  exact tcdiv 1 hG hG₀

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tdT : Tendsto (fun x => FF.dT (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.dT c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.dT
  have e := tepsX hc hc₀ hD hQ hm hq
  have g := tgi hG hG₀
  have k := tkF hc hc₀ hD hQ hm hq
  have d := tdGi hc hc₀ hD hQ hm hq hG hG₀
  have f := tdF hc hc₀ hD hQ hm hq
  have qc := tdiv hq hc hc₀.ne'
  exact ((hD.add ((e.mul g).mul k)).add ((qc.mul d).mul k)).add ((qc.mul g).mul f)

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tkZ : Tendsto (fun x => FF.kZ (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.kZ c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.kZ
  exact (tcdiv 48 hc hc₀.ne').sqrt.add ((((tcdiv 4 hc hc₀.ne').mul (tnX hc hc₀ hD hQ hm hq)).mul (tgi hG hG₀)).mul
    (tkF hc hc₀ hD hQ hm hq))

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tkDZ : Tendsto (fun x => FF.kDZ (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.kDZ c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.kDZ
  exact tendsto_const_nhds.add ((((tcdiv 12 hc hc₀.ne').sqrt.mul (tnX hc hc₀ hD hQ hm hq)).mul (tgi hG hG₀)).mul
    (tkF hc hc₀ hD hQ hm hq))

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tdZ : Tendsto (fun x => FF.dZ (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.dZ c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.dZ
  have K := tK0 hc hc₀ hD hQ hm hq
  have e := tepsX hc hc₀ hD hQ hm hq
  have g := tgi hG hG₀
  have k := tkF hc hc₀ hD hQ hm hq
  have n := tnX hc hc₀ hD hQ hm hq
  have d := tdGi hc hc₀ hD hQ hm hq hG hG₀
  have f := tdF hc hc₀ hD hQ hm hq
  have s := tsq hc hc₀
  have s0 := sq0 hc₀
  have c4 := tcdiv 4 hc hc₀.ne'
  have c8 := tcdiv 8 hc hc₀.ne'
  have c1 := tcdiv 1 hc hc₀.ne'
  have qc := tdiv hq hc hc₀.ne'
  exact (((((c8.mul hD).add (tdiv K s s0)).add
    ((((tdiv (c4.mul hD) s s0).add (tdiv K hc hc₀.ne')).mul n).mul g |>.mul k)).add
    (((c1.mul e).mul g).mul k)).add (((c1.mul qc).mul d).mul k)).add (((c1.mul qc).mul g).mul f)

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tdDZ : Tendsto (fun x => FF.dDZ (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.dDZ c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.dDZ
  have K := tK1 hc hc₀ hD hQ hm hq
  have e := tepsX hc hc₀ hD hQ hm hq
  have g := tgi hG hG₀
  have k := tkF hc hc₀ hD hQ hm hq
  have n := tnX hc hc₀ hD hQ hm hq
  have d := tdGi hc hc₀ hD hQ hm hq hG hG₀
  have f := tdF hc hc₀ hD hQ hm hq
  have s := tsq hc hc₀
  have s0 := sq0 hc₀
  have r12 := (tcdiv 12 hc hc₀.ne').sqrt
  have i1 := tcdiv 1 s s0
  have qc := tdiv hq hc hc₀.ne'
  exact ((((((tendsto_const_nhds.mul r12).mul hD).add (tdiv K s s0)).add
    ((((tdiv (r12.mul hD) s s0).add (tdiv K hc hc₀.ne')).mul n).mul g |>.mul k)).add
    (((i1.mul e).mul g).mul k)).add (((i1.mul qc).mul d).mul k)).add (((i1.mul qc).mul g).mul f)

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tdW : Tendsto (fun x => FF.dW (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.dW c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.dW
  exact (hD.mul (tkZ hc hc₀ hD hQ hm hq hG hG₀)).add (tdDZ hc hc₀ hD hQ hm hq hG hG₀)

include hc hc₀ hD hQ hm hq hG hG₀ in
theorem tnW : Tendsto (fun x => FF.nW (c x) (δD x) (δQ x) (m x) (q x) (cG x)) L
    (𝓝 (FF.nW c₀ δD₀ δQ₀ m₀ q₀ cG₀)) := by
  unfold FF.nW
  exact (tendsto_const_nhds.add (tkDZ hc hc₀ hD hQ hm hq hG hG₀)).add (tdDZ hc hc₀ hD hQ hm hq hG hG₀)

variable {δC κ δK ν δν δB M : X → ℝ} {δC₀ κ₀ δK₀ ν₀ δν₀ δB₀ M₀ : ℝ}
  (hδC : Tendsto δC L (𝓝 δC₀)) (hκ : Tendsto κ L (𝓝 κ₀)) (hδK : Tendsto δK L (𝓝 δK₀))
  (hν : Tendsto ν L (𝓝 ν₀)) (hδν : Tendsto δν L (𝓝 δν₀)) (hδB : Tendsto δB L (𝓝 δB₀)) (hM : Tendsto M L (𝓝 M₀))

include hc hc₀ hD hQ hm hq hG hG₀ hδC hκ hδK in
theorem tδCW : Tendsto (fun x => FF.δCW (c x) (δD x) (δQ x) (m x) (q x) (cG x) (δC x) (κ x) (δK x)) L
    (𝓝 (FF.δCW c₀ δD₀ δQ₀ m₀ q₀ cG₀ δC₀ κ₀ δK₀)) := by
  unfold FF.δCW
  exact (hδC.add (hδK.mul (tkZ hc hc₀ hD hQ hm hq hG hG₀))).add (hκ.mul (tdZ hc hc₀ hD hQ hm hq hG hG₀))

include hc hc₀ hD hQ hm hq hG hG₀ hν hδν in
theorem tEA2 : Tendsto (fun x => FF.EA2 (c x) (δD x) (δQ x) (m x) (q x) (cG x) (ν x) (δν x)) L
    (𝓝 (FF.EA2 c₀ δD₀ δQ₀ m₀ q₀ cG₀ ν₀ δν₀)) := by
  unfold FF.EA2
  have n := tnW hc hc₀ hD hQ hm hq hG hG₀
  have w := tdW hc hc₀ hD hQ hm hq hG hG₀
  exact (((n.mul hν).mul w).add ((n.mul hδν).mul (n.add w))).add ((w.mul (hν.add hδν)).mul (n.add w))

include hc hc₀ hD hQ hm hq hG hG₀ hδC hκ hδK hν hδν hδB hM in
theorem tEG : Tendsto (fun x => FF.EG (c x) (δD x) (δQ x) (m x) (q x) (cG x) (δC x) (κ x) (δK x) (ν x) (δν x) (δB x) (M x))
    L (𝓝 (FF.EG c₀ δD₀ δQ₀ m₀ q₀ cG₀ δC₀ κ₀ δK₀ ν₀ δν₀ δB₀ M₀)) := by
  unfold FF.EG
  have n := tnW hc hc₀ hD hQ hm hq hG hG₀
  exact (((((tendsto_const_nhds.mul hν).mul (n.pow 2)).add
    (tendsto_const_nhds.mul ((tδCW hc hc₀ hD hQ hm hq hG hG₀ hδC hκ hδK).pow 2))).add
    (tendsto_const_nhds.mul ((tdT hc hc₀ hD hQ hm hq hG hG₀).pow 2))).add
    ((tendsto_const_nhds.mul hM).mul (hδB.pow 2))).add (tEA2 hc hc₀ hD hQ hm hq hG hG₀ hν hδν)

end FFlim

namespace FFlimN

variable {X : Type*} {L : Filter X} {EGv nWv dWv δCWv dTv ν δν δB M cg qb : X → ℝ}
  {EG₀ nW₀ dW₀ δCW₀ dT₀ ν₀ δν₀ δB₀ M₀ cg₀ qb₀ : ℝ}
  (hEG : Tendsto EGv L (𝓝 EG₀)) (hnW : Tendsto nWv L (𝓝 nW₀)) (hdW : Tendsto dWv L (𝓝 dW₀))
  (hδCW : Tendsto δCWv L (𝓝 δCW₀)) (hdT : Tendsto dTv L (𝓝 dT₀)) (hν : Tendsto ν L (𝓝 ν₀))
  (hδν : Tendsto δν L (𝓝 δν₀)) (hδB : Tendsto δB L (𝓝 δB₀)) (hM : Tendsto M L (𝓝 M₀))
  (hcg : Tendsto cg L (𝓝 cg₀)) (hcg₀ : cg₀ ≠ 0) (hqb : Tendsto qb L (𝓝 qb₀))

include hcg hcg₀ hqb in
theorem tX0 : Tendsto (fun x => FF.X0 (cg x) (qb x)) L (𝓝 (FF.X0 cg₀ qb₀)) := by
  unfold FF.X0; exact tdiv hqb hcg hcg₀

include hcg hcg₀ hqb hδB in
theorem tY0 : Tendsto (fun x => FF.Y0 (cg x) (qb x) (δB x)) L (𝓝 (FF.Y0 cg₀ qb₀ δB₀)) := by
  unfold FF.Y0; exact (tcdiv 2 hcg hcg₀).mul (hqb.add hδB)

include hcg hcg₀ hqb hν hnW in
theorem tPx : Tendsto (fun x => FF.Px (ν x) (nWv x) (cg x) (qb x)) L (𝓝 (FF.Px ν₀ nW₀ cg₀ qb₀)) := by
  unfold FF.Px FF.Ex
  exact ((hqb.mul (tX0 hcg hcg₀ hqb)).add ((hν.mul (hnW.pow 2)).mul ((tX0 hcg hcg₀ hqb).pow 2))).sqrt

include hcg hcg₀ hqb hν hnW hEG hδB in
theorem tPy : Tendsto (fun x => FF.Py (EGv x) (ν x) (nWv x) (cg x) (qb x) (δB x)) L
    (𝓝 (FF.Py EG₀ ν₀ nW₀ cg₀ qb₀ δB₀)) := by
  unfold FF.Py FF.Ey
  have y := tY0 hδB hcg hcg₀ hqb
  exact ((tendsto_const_nhds.mul ((hEG.mul (y.pow 2)).add (y.mul (hqb.add hδB)))).add
    ((hν.mul (hnW.pow 2)).mul (y.pow 2))).sqrt

include hdW hnW hν hδν in
theorem tKD : Tendsto (fun x => FF.KD (dWv x) (nWv x) (ν x) (δν x)) L (𝓝 (FF.KD dW₀ nW₀ ν₀ δν₀)) := by
  unfold FF.KD
  exact (hdW.mul ((hν.add hδν).mul (hnW.add hdW))).add (hnW.mul ((hδν.mul (hnW.add hdW)).add (hν.mul hdW)))

include hEG hnW hdW hδCW hdT hν hδν hδB hM hcg hcg₀ hqb in
theorem tEN : Tendsto (fun x => FF.EN (EGv x) (nWv x) (dWv x) (δCWv x) (dTv x) (ν x) (δν x) (δB x) (M x) (cg x) (qb x)) L
    (𝓝 (FF.EN EG₀ nW₀ dW₀ δCW₀ dT₀ ν₀ δν₀ δB₀ M₀ cg₀ qb₀)) := by
  unfold FF.EN
  have X := tX0 hcg hcg₀ hqb
  have Y := tY0 hδB hcg hcg₀ hqb
  have Px := tPx hnW hν hcg hcg₀ hqb
  have Py := tPy hEG hnW hν hδB hcg hcg₀ hqb
  have K := tKD hnW hdW hν hδν
  have sM := hM.sqrt
  exact (((((hδB.mul Y).add (X.mul hδB)).add (((hδCW.mul X).mul (Py.add (hδCW.mul Y))).add (Px.mul (hδCW.mul Y)))).add
    ((K.mul X).mul Y)).add (((hdT.mul X).mul (Py.add (hdT.mul Y))).add (Px.mul (hdT.mul Y)))).add
    ((((hδB.mul X).mul (sM.mul Py)).add (((hM.mul (hδB.pow 2)).mul X).mul Y)).add (((sM.mul Px).mul hδB).mul Y))

end FFlimN

#print axioms FFlim.tEG
#print axioms FFlimN.tEN

end AdalyFormal.DLayer
