from pathlib import Path
import json,re
D=Path('AHP/round4/guarded/mine')
idx=json.loads((D/'index.json').read_text())
selected={}
def add(d):selected[d['name']]=dict(d)
# Semantic over-approximation of the actual compiled dependency closure.
for d in idx.values():
 if not d['roots'] or d['kind'] not in ('theorem','lemma'):continue
 h=d['header'];n=d['name']
 if (re.search(r'Ginv|G1inv|Delta2|delta2|C2fullOf|C2full|D2Step|C2Step|C2Comp|psiD|Jf_split|holRegime|hC2|Jcov|J_local|G1_coer|unitR|H_l2|H1_l2|Wop.*congr|G_congr|data_congr|rightInv|[Ww]ellDef|w4_class|OpLayer',h) and re.search(r'≤|<|IsUnit|Injective|=|↔|WellDef|OpLayer',h)) or re.search(r'rawStep_congr|congr_bg|congr_in|congr_U',n):add(d)
# Include the public neighbors needed to state scope, units, norm estimates and locality explicitly.
modules={
'TT_A':None,'TT_B':None,'TT_C':None,'TT_F':None,'TT_Z':['ballChartsGT_proved'],
'MX_A':None,'MX_B':None,'MXQ_A':None,'MXQ_B':None,
'MX_F':None,'MXQ_F':None,'MXQ_Tor':None,'MXQ_Br':None,
'AU_SK3':None,'AC_SK3':None,'AC_MR4':None,'MR2':['patchCoercive_charts','patchCoercive_charts_exists'],
'MI2':['PatchCoercive','GinvIMS','ginv_weighted_coercive_of'],
'MI21':None,'MI22':['ginv_weighted_coercive'],
'MI28':['ginv_weighted_coercive_M1'], 'MI33':['ginv_weighted_coercive_full','wellDef_strat','wellDef_strat_small'],
'MI34':['ginv_congr_U','ginv_weighted_coercive_loc','wellDef_strat_loc'],
'MA18':['cwW4_lower'], 'MA13':['cw_uniform'],
'UMC':['a1D','a1D_pos','dlayer_explicit'],
'AC_MZ5':None,'MZ5':None,'AC_OL8':None,'OL8':None,'AC_MZ3':None,'MZ3':['Jf_split','Jf_covered'],
'AC_MZ4':['col_classAC'],'MZ4':['Ageo','col_class'],
'MX_AC_MZ5':None,'MXQ_AC_MZ5':None,'MX_C':['dlayer_explicitΦ'],'MXQ_C':['dlayer_explicitΦ'],
'DQ5':['C2full_strat','dqSmall_exists','K2strat_mono','C2full_strat_window'],
'OL2':['C2full_strat12','C2row_congr_U','hC2_class'],
'DS1':None,'DY2':['C2row_congr','polar_row_ball'],'DY3':['C2row_level0','delta2_bil','delta2_conj'],
'M1B':['DLayerStrat','wnormSq'],
'MZ5':['OpLayer','dlayerStrat_class','DLayerObligationClass','dlayerObligationClass_holds'],
'OL6':['H_l2_colR'],'OL7':['G1_coerR','G1_unitR','N1_unitR','H1_l2_colR','H1_eqR'],
'OL9':['qs_inj_of_hext','hHL2_cfg'],
'DH1':['Ginv_unit','Ginv_G','G_Ginv','N_unit','H_col'],
'DC2':['cjp_form_lower','N_lower','N_cjp_coer','H_cjp_w'],
'OL14':['ginv_upper_cov','hext_of_rightinv_cov'],'RI2':['Dvec_supp','Tvec_supp','Tlin_rightInv'],
'RI5':['num_RI','rightInv_cfg','classRightInvCov','classRightInv'], 'RI6':None,
'TL22a':['guardsUnit_of_fields'], 'AC_SV1':None,'TL13b':['HDesc.inverse'],'TL3c':['isUnit_of_desc','Desc.inverse'],
'TL15b':['BDLink.G','BDLink.H','BDLink.G1inv'],'TL15c':['BDLink.H1'],
'ZXG3A':['GenP.WellDef','GenP.Nmat'],'ZT4A':['GenP.GuardsUnit','GenP.WellDefG'],
'ZR8Site':['Gp_congr','Rproj_congr','RImage_support','Wop_congr_both','DpiFull_congr'],
'ZR8DataB':None,'ZR8DataA':['QfullOf_congr','C2fullOf_congr_U','C2fullOf_congr_in','sector_congr'],
'ZR8Jet':None,'ZR8Data':['Q1_rows_congr','C2tilde_rows_congr','H0_congr_rows','hLift_congr_rows','D2in_congr','WellDef_congr','GuardsUnit_congr','WellDefG_congr'],
'R2Algebra':['Ginv','G','H','IsG1inv','exists_G1inv','G1inv_unique','delta2Bil','Delta2','Delta2_spec','isG1inv_sub','G1inv_coercive','isUnit_Q_inv_Qs','G1','H1','QG1Qs_isUnit','QG1Qs_isUnit_of_small','inverse_sub_eq_tsum'],
'DLR1':['coercive_isUnit','coercive_apply_inverse','coercive_inv_bound'],
'D1Lit':['pin_target8','pin_target8_iff','pin_genForm'],
'GdStat':None,'GdGen3':None,'GdGen4':['NG_unit_of_N1','unit_transfer','twoData_lit_loc'],
'GdGen8':['WellDefAt_loc_of_inst'], 'GdGap':['WellDefAt','GapAt','P428Target8SG2','localised_SG2_holds'],
'GdGen2':['V0','dataS_C2_eq','C2full_level0_coord'],
'GdGen5':['genFormS_eq_loc'],'GdGen7':['GapAt_of_loc','InstIneqSG_general'],
'GdGen9':['P428Target8SG_of_residual'], 'GdR5a':['P428Target8SG_iff_residualT'],
'DrRed1':None,'DrEquiv':None,
}
for d in idx.values():
 mod=Path(d['file']).stem
 if mod not in modules:continue
 names=modules[mod]
 if names is None or any(d['name'].endswith('.'+n) for n in names):add(d)
# Remove false-positive scalar/cutoff/gauge-construction hits and source-only utilities.
for n in list(selected):
 if n in ('AdalyFormal.LemIFlat.scalar_core','AdalyFormal.M1Assembly.gam1_ge','AdalyFormal.M2Glue3.glue_zstep') or n.startswith('MXQ.Total.embedFam') or n.endswith(('mem_embedFam','isClassCubeQ_embed','classCoupledQ_embed')):selected.pop(n)
# Definitions of the precise proposition shapes, not new premises.
for d in idx.values():
 if d['name'].endswith(('.OpLayer','.InstAtWD','.CoercG8AtWD','.P428Target8','.ClassSmall')) and d['roots']:add(d)
rows=sorted(selected.values(),key=lambda d:(d['file'],d['line']))
for i,d in enumerate(rows,1):d['id']=f'D{i:03}'
(D/'manifest.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
imports=['TT_F','MXQ_Br','MXQ_Tor','DrEquiv','MI34','DLR1']
s=''.join('import '+m+'\n' for m in imports)+'\nset_option maxHeartbeats 16000000\nset_option maxRecDepth 8000\nset_option format.width 120\nset_option pp.proofs false\nset_option pp.deepTerms true\n\n'
for d in rows:
 s+=f'-- {d["id"]} {d["file"]}:{d["line"]}\n#check {d["name"]}\n#print axioms {d["name"]}\n\n'
s+='\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n'
for d in rows:
 s+=f'  let n := ``{d["name"]}\n  match env.getModuleIdxFor? n with\n  | some i => logInfo m!"ORIGIN|{{n}}|{{env.header.moduleNames[i.toNat]!}}"\n  | none => throwError m!"missing module for {{n}}"\n'
(D/'ChecksV3.lean').write_text(s)
print('selected',len(rows),'imports',imports)
missing=[]
for m,ns in modules.items():
 if ns:
  for n in ns:
   if not any(Path(d['file']).stem==m and d['name'].endswith('.'+n) for d in rows):missing.append((m,n))
print('unmatched requests',missing)
