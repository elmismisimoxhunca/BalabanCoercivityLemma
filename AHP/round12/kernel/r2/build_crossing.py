#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent; ROOT=H.parents[3]
p=ROOT/'AHP/round9/qualitative-r2/Attempt.lean'; s=p.read_text()
a=s.index('omit [FiniteDimensional ℝ E] in\ntheorem abs_inner_le_opNorm')
b=s.index('/-- The end of the initial positive semidefinite interval',a)
helpers=s[a:b]
a2=s.index('  set S : Set ℝ := {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}',b)
b2=s.index('  have hbef :',a2)
body=s[a2:b2]+'  exact ⟨hts0\', hts1\', hpsd_ts, hnu, hle, haft⟩\n'
header='''
namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Set
open AdalyFormal.D1Literal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
'''
statement='''
/-- Continuity and endpoint signs already give a singular PSD edge strictly
between the endpoints. No isolated-nonunit hypothesis is needed for these clauses. -/
theorem psdEdge_singular_without_isolation (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0) := by
'''
proof=header+helpers+statement+body+'''\n#print axioms psdEdge_singular_without_isolation
end AdalyFormal.Round9.Guarded.QualitativeR2
'''
text=(ROOT/'AHP/round12/kernel/r1/ActualKernel.lean').read_text()+proof+(H/'CrossingAppendix.lean.txt').read_text()
(H/'ActualCrossing.lean').write_text(text)
(H/'CROSSING_COPIES.json').write_text(json.dumps({'prefix':{'path':'AHP/round12/kernel/r1/ActualKernel.lean','sha256':hashlib.sha256((ROOT/'AHP/round12/kernel/r1/ActualKernel.lean').read_bytes()).hexdigest()},'helpers':{'path':str(p.relative_to(ROOT)),'start_line':s[:a].count('\n')+1,'end_line':s[:b].count('\n')+1,'sha256':hashlib.sha256(helpers.encode()).hexdigest()},'proof_reuse':'psdEdge_spec proof through hnu, excluding unused isolated-nonunit hbef clause'},indent=2)+'\n')
print('wrote',len(text.splitlines()),'lines')
