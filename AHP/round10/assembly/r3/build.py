#!/usr/bin/env python3
"""Assemble compact concrete glue from verified prior bodies; never compile historical Attempt."""
from pathlib import Path
import re,json,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
R9=ROOT/'AHP/round9/qualitative-r2/Attempt.lean'
R2=ROOT/'AHP/round10/shared/assembly/R2_SourceGlue.lean'
manifest=[]
def decl(path,name):
 s=path.read_text();m=re.search(r'^(?:(?:noncomputable )?def|theorem|abbrev|lemma) '+re.escape(name)+r'\b',s,re.M);assert m,(path,name)
 n=re.search(r'\n(?:(?:noncomputable )?def |theorem |abbrev |lemma |open |end |namespace |section|variable |include |omit |#print |/[-!])',s[m.end():])
 e=m.end()+n.start()+1 if n else len(s)
 out=s[m.start():e].rstrip()+'\n'
 manifest.append(dict(name=name,source=str(path.relative_to(ROOT)),line=s[:m.start()].count('\n')+1,sha256=hashlib.sha256(out.encode()).hexdigest()))
 return out
base='''open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
'''
q='AdalyFormal.Round9.Guarded.Qualitative';q2=q+'R2';qj=q2+'Joint'
a2='AdalyFormal.Round9.Guarded.AnalyticR2'
def ns(name,names,path=R9,extra=''):
 return '\nnamespace '+name+'\n'+base+extra+'\n'+''.join(decl(path,n)+'\n#print axioms '+n+'\n' for n in names)+'\nend '+name+'\n'
parts=[]
parts.append(ns(q,['pathU','pathP','pathA','uthPath','vacA']))
parts.append(ns(q2,['bulkD','bulkD_rot']))
parts.append(ns(qj,['corrDeriv']))
parts.append(ns(q,['scalar_on_complex_line'],extra='variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n'))
parts.append(ns(q2,['psdEdge'],extra='open AdalyFormal.D1Literal (PSD)\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n'))
parts.append(ns(q2,['vacEdge','CanonicalCoupling']))
parts.append(ns(q2,['AnM','AnFam'],extra='variable {L : PeriodicLatticeExtent}\nopen AdalyFormal.D1Literal (SU2m)\n'))
parts.append(ns(qj,['CofinalAnyProfileCoupling','CofinalAnyPathCoupling']))
parts.append(ns('AdalyFormal.Round10.Dictionary',['comm_of_quad','deriv_comm'],R2,extra='variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n'))
parts.append(ns('AdalyFormal.Round10.Dictionary.Actual',['bulkD_U1','corrDeriv_U1'],R2))
parts.append(ns('AdalyFormal.Round10.Assembly.R2',['deriv_symmetric','corrDeriv_symmetric','KernelLine','canonicalCoupling_of_line'],R2))
parts.append(ns(a2,['tendsto_clm_apply₂','tendsto_Delta2_div_form','limit_Delta2_div_form'],extra='open ContinuousLinearMap\n'))
prereq='\n'.join(parts)
def put(path,content):
 data=content.encode() if isinstance(content,str) else content
 if not path.exists() or path.read_bytes()!=data:path.write_bytes(data)
put(HERE/'GluePrereq.lean',prereq)
basepath=ROOT/'AHP/round10/dictionary/r3/Actual.lean'
# Snapshot only the stable energy portion; do not copy a concurrently edited later proof.
s=basepath.read_text(); end=s.index('\ntheorem fixed_of_slope_limit')
energy_names=['circulation_congr_boundary','circulation_interiorProfile','responseProfile','profileCoupling',
 'profileCoupling_curl','adaptive_energy','adaptive_nonneg','CurlDetected','adaptive_pos_iff',
 'exists_profile_iff_curlDetected','all_profiles_zero_iff','responseProfile_off','responseProfile_interior','liftJet_Q']
energy_slice=s[:end]+'\n'+''.join('#print axioms '+n+'\n' for n in energy_names)+'\nend AdalyFormal.Round10.Dictionary.FreeSource\n'
put(HERE/'DictionaryEnergySlice.lean',energy_slice)
put(HERE/'Compact.lean',energy_slice.encode()+b'\n'+prereq.encode()+b'\n'+(HERE/'NeutralAppendix.lean').read_bytes()+b'\n'+(HERE/'EnergyGlue.lean').read_bytes())
fluxpath=ROOT/'AHP/round10/nonvanishing/r3/DilatedFlux.lean'
flux=fluxpath.read_text().replace('import DrEquiv\n','').replace('import ZXR2Flat6\n','')
for name in ['dilLu','dilTower']:
 body=decl(fluxpath,name)
 assert body in flux
 flux=flux.replace(body,'')
# Only consume the stable physical theorem; dictionary supplies its own neutral functional.
a=flux.index('\nnoncomputable def neutralFunctional'); b=flux.index('\n#print axioms L',a)
flux=flux[:a]+flux[b:]
put(HERE/'FluxAppendix.lean',flux)
jets=(ROOT/'AHP/round10/dictionary/r3/JetAppendix.lean').read_text()
end=jets.index('/-- The two tracks use the same physical aggregate')
jets=jets[:end]+''.join('#print axioms '+n+'\n' for n in ['neutralFunctional','physicalJetAggregate','curlDetected_of_physicalJet','adaptive_pos_of_physicalJet','exists_profile_of_physicalJet'])+'end AdalyFormal.Round10.Dictionary.JetDetection\n'
put(HERE/'DictionaryJetSlice.lean',jets)
put(HERE/'JetCompact.lean',(HERE/'Compact.lean').read_text().replace('import DrEquiv\n','import DrEquiv\nimport ZXR2Flat6\n',1)+'\n'+flux+'\n'+jets+'\n'+(HERE/'JetGlue.lean').read_text())
# Historical assembly: preserve all R9 bytes and the earlier R2 appendix unchanged.
r2attempt=(ROOT/'AHP/round10/assembly/r2/Attempt.lean').read_bytes()
assert r2attempt.startswith(R9.read_bytes())
energy_appendix='noncomputable section\n'+energy_slice[energy_slice.index('namespace AdalyFormal.Round10.Dictionary.SourceEnergy'):]
put(HERE/'EnergyAppendix.lean',energy_appendix)
# These two geometry theorems already occur in the unchanged round-9 prefix.
histflux=flux
for name in ['dil_unit_size','dil_fine_size']:
 body=decl(fluxpath,name)
 assert body in histflux
 histflux=histflux.replace(body,'')
put(HERE/'HistoricalFluxAppendix.lean',histflux)
newparts=[energy_appendix,(HERE/'NeutralAppendix.lean').read_text(),(HERE/'EnergyGlue.lean').read_text(),
 histflux,jets,(HERE/'JetGlue.lean').read_text(),(HERE/'GoalBridge.lean').read_text(),(HERE/'HistoricalJetBridge.lean').read_text()]
put(HERE/'Attempt.lean',r2attempt+b'\n'+('\n'.join(newparts)).encode())
put(HERE/'COPIES.json',json.dumps(manifest,indent=2)+'\n')
print('Compact lines',len((HERE/'Compact.lean').read_text().splitlines()))
print('JetCompact lines',len((HERE/'JetCompact.lean').read_text().splitlines()))
print('Attempt prefix exact',(HERE/'Attempt.lean').read_bytes().startswith(R9.read_bytes()),'; NOT COMPILED')
put(HERE/'Neutral.lean',(ROOT/'AHP/round10/shared/dictionary/R2_SourceDictionary.lean').read_bytes()+b'\n'+(HERE/'NeutralAppendix.lean').read_bytes())
for local,published in [('Neutral.lean','R3_NeutralResponse.lean'),('Compact.lean','R3_EnergyGlue.lean'),('JetCompact.lean','R3_JetGlue.lean')]:
 put(ROOT/'AHP/round10/shared/assembly'/published,(HERE/local).read_bytes())
