#!/usr/bin/env python3
"""Publish the exact, typechecked physical statement left open by R1.

This file only assembles existing compiled declarations and the new gap
statement.  It does not assert or generate a proof of that statement.
"""
from pathlib import Path

H = Path(__file__).resolve().parent
ROOT = H.parents[3]
base = (ROOT / "AHP/round14/shared/transfer/R2_Collar.lean").read_text()
collar = (H / "Collar.lean").read_text()
# Imports are legal only at the start of a Lean file.  The base already has
# both frozen imports used by the model certificate.
collar_body = collar.split("import DrEquiv\n", 1)[1]

GAP = r'''

namespace AdalyFormal.Round15.Dictionary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round10.Nonvanishing.DilatedFlux
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Detection.ColorArea

/-- The eight actual charged coordinates on one fine collar layer.  The first
coordinate is a site on the physical 256-point longitudinal torus; the two
transverse coordinates range over the physical eight-point circles. -/
def physicalLayer (u : TwistSpace 1 20) (x : Fin (12*1*20+16)) : Fin 8 → ℂ :=
  fun i =>
    let d : Fin 3 := if i.val < 4 then 1 else 2
    let c : Fin 4 := if h : i.val < 4 then ⟨i.val, by omega⟩ else ⟨i.val-4, by omega⟩
    let yz : Fin 8 × Fin 8 := ![(0,0),(1,0),(0,1),(1,1)] c
    let site : PeriodicLatticeSite (scaleUp 2 1 (dilLu 1 20)) :=
      Function.update (Function.update (Function.update (rightSite (q := 1) (by norm_num) 20) 0 x) 1 yz.1) 2 yz.2
    (AdalyFormal.Round13.Detection.ColorArea.realPart (G 1 20) u (site,d) : ℂ) +
      (AdalyFormal.Round13.Detection.ColorArea.imagPart (G 1 20) u (site,d) : ℂ) * Complex.I

/-- Exact physical statement still unproved in R1: every original charged
right-star kernel-line vector satisfies the extracted constant blocks on the
deep flat-collar rows.  This is a definition of the remaining obligation, not
an inhabitant or a physical-area-seed proof. -/
def Q1C10PhysicalDictionary : Prop :=
  ∀ u : TwistSpace 1 20,
    KernelLine 1 20 (rightStar (q := 1) (by norm_num) 20) u →
    ∀ x : Fin (12*1*20+16), 213 ≤ x.val → x.val ≤ 250 →
      Matrix.mulVec collarC (physicalLayer u (x-1)) +
        Matrix.mulVec collarB (physicalLayer u x) +
        Matrix.mulVec collarA (physicalLayer u (x+1)) = 0

#print axioms physicalLayer
#print axioms Q1C10PhysicalDictionary

end AdalyFormal.Round15.Dictionary
'''

text = base + collar_body + GAP
(H / "PhysicalGap.lean").write_text(text)
shared = H.parents[1] / "shared/dictionary"
shared.mkdir(parents=True, exist_ok=True)
(shared / "R1_PhysicalGap.lean").write_text(text)
print("wrote", H / "PhysicalGap.lean", shared / "R1_PhysicalGap.lean", "lines", len(text.splitlines()))
