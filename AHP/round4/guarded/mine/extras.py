from pathlib import Path
import json
D=Path('AHP/round4/guarded/mine')
idx=json.loads((D/'index.json').read_text())
base=json.loads((D/'manifest.json').read_text())
modules={'CJ4':['classSmall_exists'],'OL11':['ClassRightInv','OpLayerThick'],'OL15':['ClassRightInvCov'],'OG8':['FieldsKAt','FieldsK'],'OG9':['fieldsK_of_ball'],'SK1':['ClassFam'],'BallCharts':['BallChartsAtG','BallChartsG'],'D2Cons':['InstIneqSG','CoercG8AtSG','P428Target8SG']}
names={d['name'] for d in base};extra=[]
for d in idx.values():
 if Path(d['file']).stem in modules and d['name'] not in names and any(d['name'].endswith('.'+n) for n in modules[Path(d['file']).stem]):extra.append(d)
rows=sorted(base+extra,key=lambda d:(d['file'],d['line']))
for i,d in enumerate(rows,1):d['id']=f'D{i:03}'
(D/'manifestCore.json').write_text(json.dumps(base,ensure_ascii=False,indent=2))
(D/'manifest.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
s=''.join('import '+m+'\n' for m in ['TT_F','MXQ_Br','MXQ_Tor','DrEquiv','MI34','DLR1'])+'\nset_option maxHeartbeats 16000000\nset_option maxRecDepth 8000\nset_option format.width 120\nset_option pp.proofs false\nset_option pp.deepTerms true\n\n'
for d in extra:s+=f'#check {d["name"]}\n#print axioms {d["name"]}\n\n'
s+='\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n'
for d in extra:s+=f'  let n := ``{d["name"]}\n  match env.getModuleIdxFor? n with\n  | some i => logInfo m!"ORIGIN|{{n}}|{{env.header.moduleNames[i.toNat]!}}"\n  | none => throwError m!"missing module for {{n}}"\n'
(D/'ChecksExtra.lean').write_text(s)
print('Supplement',len(extra),'total',len(rows))
