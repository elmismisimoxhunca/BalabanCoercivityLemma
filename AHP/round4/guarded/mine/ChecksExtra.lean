import TT_F
import MXQ_Br
import MXQ_Tor
import DrEquiv
import MI34
import DLR1

set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option format.width 120
set_option pp.proofs false
set_option pp.deepTerms true

#check AdalyFormal.OneGap.BallChartsAtG
#print axioms AdalyFormal.OneGap.BallChartsAtG

#check AdalyFormal.OneGap.BallChartsG
#print axioms AdalyFormal.OneGap.BallChartsG

#check AdalyFormal.ClassJets.classSmall_exists
#print axioms AdalyFormal.ClassJets.classSmall_exists

#check AdalyFormal.D1Literal.InstIneqSG
#print axioms AdalyFormal.D1Literal.InstIneqSG

#check AdalyFormal.D1Literal.CoercG8AtSG
#print axioms AdalyFormal.D1Literal.CoercG8AtSG

#check AdalyFormal.D1Literal.P428Target8SG
#print axioms AdalyFormal.D1Literal.P428Target8SG

#check AdalyFormal.OneGap.FieldsKAt
#print axioms AdalyFormal.OneGap.FieldsKAt

#check AdalyFormal.OneGap.FieldsK
#print axioms AdalyFormal.OneGap.FieldsK

#check AdalyFormal.OneGap.fieldsK_of_ball
#print axioms AdalyFormal.OneGap.fieldsK_of_ball

#check AdalyFormal.M2OpLayer.ClassRightInv
#print axioms AdalyFormal.M2OpLayer.ClassRightInv

#check AdalyFormal.M2OpLayer.OpLayerThick
#print axioms AdalyFormal.M2OpLayer.OpLayerThick

#check AdalyFormal.M2OpLayer.ClassRightInvCov
#print axioms AdalyFormal.M2OpLayer.ClassRightInvCov

#check AdalyFormal.M2Skel.ClassFam
#print axioms AdalyFormal.M2Skel.ClassFam


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let n := ``AdalyFormal.OneGap.BallChartsAtG
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.OneGap.BallChartsG
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.ClassJets.classSmall_exists
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.InstIneqSG
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.CoercG8AtSG
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.D1Literal.P428Target8SG
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.OneGap.FieldsKAt
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.OneGap.FieldsK
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.OneGap.fieldsK_of_ball
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.ClassRightInv
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.OpLayerThick
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2OpLayer.ClassRightInvCov
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
  let n := ``AdalyFormal.M2Skel.ClassFam
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"ORIGIN|{n}|{env.header.moduleNames[i.toNat]!}"
  | none => throwError m!"missing module for {n}"
