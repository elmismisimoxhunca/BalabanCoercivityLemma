from pathlib import Path
import json,re,hashlib
from source_utils import signature_end
D=Path('AHP/round4/guarded/mine'); root=D.parent
rows=json.loads((D/'manifest.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
records={};origins={}
for file in ['ChecksV3.lean','ChecksExtra.lean']:
 log=(D/(file+'.log')).read_text()
 assert (D/(file+'.exit')).read_text().strip()=='0'
 assert not re.search(r'error:|warning:',log)
 first=re.search(r'^#check (.+)$',(D/file).read_text(),re.M)[1]
 start=log.index(first)
 for m in re.finditer(r"^'(.+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",log,re.M):
  name=m[1];typ=log[start:m.start()].strip();ax={x.strip() for x in (m[3] or '').split(',') if x.strip()}
  assert ax<=allowed,(name,ax)
  assert typ.startswith((name+' ',name+':',name+'.{',name+'\n')),(name,typ[:120])
  assert name not in records,name
  records[name]={'type':typ,'axioms':sorted(ax),'axiomLine':m[0].strip(),'auditFile':str(D/file)};start=m.end()
 for m in re.finditer(r'^ORIGIN\|([^|]+)\|(.+)$',log,re.M):origins[m[1]]=m[2]
assert len(records)==len(rows),(len(records),len(rows))
for d in rows:assert origins.get(d['name'])==Path(d['file']).stem,(d['name'],origins.get(d['name']),d['file'])
# Preserve verbatim source signatures, and definition bodies for proposition shapes.
def strip_comments(s):
 out=[];dep=0;i=0
 while i<len(s):
  if s[i:i+2]=='/-':dep+=1;out.extend('  ');i+=2
  elif dep and s[i:i+2]=='-/':dep-=1;out.extend('  ');i+=2
  elif dep:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(s[i]);i+=1
 return ''.join(out)
def source(d):
 raw=Path(d['file']).read_text();cl=strip_comments(raw); ls=raw.splitlines(keepends=True);st=sum(map(len,ls[:d['line']-1])); rest=cl[st:]
 if d['kind'] in ('theorem','lemma'):
  cut=signature_end(rest);assert cut is not None,d['name'];return raw[st:st+cut].rstrip()
 else:
  nxt=re.search(r'\n(?:namespace\b|end\b|section\b|variable\b|open\b|#|set_option\b|(?:noncomputable\s+|protected\s+)*(?:def|abbrev|theorem|lemma|structure|instance)\s)',rest)
  en=nxt.start() if nxt else len(rest)
  en=len(rest[:en].rstrip());return raw[st:st+en].rstrip()
def selector(d):
 n=d['name']; m=Path(d['file']).stem
 if n.split('.')[-1] in ('ClassFam','ClassFamT'):return 'Selector-neutral generic class-quantifier wrapper. Applications in the mined proofs use localized operators; an arbitrary predicate parameter is not evidence for selAll.'
 if m=='CJ4':return 'Selector-independent numeric smallness predicate/window for the shared raw-jet chart; it does not estimate exterior all-plaquette curvature or any inverse.'
 if m=='BallCharts':return 'Selector-independent chart ingredients on the specified balls/class. They do not add coverage or regularity on omitted exterior plaquettes.'
 if m in ('OG8','OG9'):return 'Frozen site/row/mass/chart and Q-adjoint-injectivity ingredients, common to the selector constructions at this scope; no Ginv_all or boundary-response estimate follows from the shape alone.'
 if m in ('R2Algebra','DLR1','DC2','DY4a') or n.startswith('AdalyFormal.D1Guarded.TwoData.') or n.endswith(('.stat_eq','.NG_unit_of_N1','.unit_transfer')):
  return 'Selector-neutral conditional algebra. Either selector may be substituted only after proving every displayed premise; this does not discharge them for selAll.'
 if m.startswith('Gd') or m in ('DrRed1','DrEquiv','D1Collapse'):
  if n.endswith('.WellDefAt_loc_of_inst'):return 'selIn only (conclusion explicitly WellDefAt selIn selIn); requires the localized inequality and a positive-energy competitor.'
  return 'Explicit-selector/bridge result: includes selAll where the exact type permits, with every unit, subspace and geometry premise retained. Not unconditional class coercivity for selAll.'
 if m=='D2Cons':return 'Explicit selector-parametric Ginv-only guarded statement; selAll is an open instance, selIn a proved instance elsewhere. These definition entries prove neither.'
 if m=='D1Lit':
  if n.split('.')[-1].startswith('pin_'):return 'Exact identification with selIn selIn. No selAll conclusion.'
  return 'Selector-parametric definition/form identity for either selector; existence of a representing G1inv operator is not IsUnit G1inv.'
 if m=='DLR58':return 'Local stencil/source estimate for the displayed LocRep and full Jfield; applies to either assembly only on stencils satisfying those premises. It does not control arbitrary exterior plaquettes.'
 if n.endswith(('.hC2_class','.C2full_strat12')):return 'Selector-independent raw C2fullOf bound on its stated chart/smallness class; usable as a common ingredient for selAll and selIn. It does not bound either inverse or exterior curvature.'
 if m.startswith(('ZR8Jet','ZR8Read','DLR27','DLR67','DLR69','DLR72','DLR73','DQ')) or m in ('DY1','DY2','GCa3L','GCa4','CJ2') or n.endswith(('.C2row_level0','.C2fullOf_congr_in','.C2fullOf_congr_U','.C2row_congr_U','.C2full_level0_coord','.C2full_norm','.gauge_C2full_norm')):
  return 'Raw-jet/common-ingredient fact, independent of the plaquette selector; usable for either assembly at this scope. It does not propagate support through G or G1.'
 if m in ('ZR8Site','AC_MZ4','MZ4') or n.endswith(('.Gp_congr','.RImage_support','.Wop_congr_both')):
  return 'Localized/common ingredient as named in the type. Gp/Wop do not change with the selector; a bound/congruence for them is not one for Ginv_all. DpiFull uses selIn.'
 if m.startswith('TL'):
  return 'Generic covering/intertwining algebra when abstract; concrete BDLink/guardsUnit uses selIn. No unconditional inverse locality for selAll.'
 if m in ('RI2','RI3','RI4','RI5'):
  return 'Q/right-inverse construction common to both selectors, or its localized Ginv-energy bound as explicitly stated; not a right inverse of Ginv_all.'
 if m in ('ZT4A','ZXG3A','ZT5A','TT_A','MX_A','MXQ_A') or d['kind'] in ('def','abbrev','structure'):
  return 'Shape/definition or auxiliary ingredient for the frozen localized (selIn) chain, not itself a proof. See the exact body; changing class factors/families does not select selAll.'
 return 'selIn: frozen gparams/P.data/G1inv/localized class chain (or its patch/conditional ingredient). No selAll class estimate is asserted.'
def order(d):
 n=d['name'];s=n.split('.')[-1];h=d['header'];m=Path(d['file']).stem
 if s in ('ClassSmall','classSmall_exists'):return 'ClassSmall is an explicit numeric predicate with no chosen witnesses. classSmall_exists: ell -> a0>0 -> every 0<=a<=a0 satisfies it. Here a denotes the small class parameter, not the mass parameter.'
 if s in ('ClassRightInv','ClassRightInvCov'):return 'ell>=2,a>0 -> m1 -> m>=m1 -> bN>0 (energy version) or cW,cG>=0 (covariant version) -> R1 -> R>=R1 -> s>0 -> k,Lu,alpha0,S,Lam,U -> source -> preimage. These older constants may depend on m, and the cap on R.'
 if s in ('ClassFam','OpLayerThick','opLayerThick_of','BallChartsG'):return 'Fix ell (and a where present, plus the stated family premises for the theorem) -> m1 -> m>=m1 -> R1 -> R>=R1 -> Cs-valued analytic constants and s>0 -> k,Lu,alpha0,S,Lam,U. This is older ClassFam order, not Total order.'
 if s in ('FieldsK','fieldsK_of_ball'):return 'ell,a and any ball-chart-family premise -> df,m1 -> m>=m1 -> R1 -> R>=R1 -> K>=1,s>0 -> k,Lu,alpha0,S,Lam,U. In this older shape K may depend on m,R.'
 if s=='P428Target8SG':return 'ell>=2,a>0 -> m0>=1 -> m>=m0 -> R0 -> R>=R0 -> a0>0,gamma0>0 -> k,Lu,alpha0,S,Lam,U -> IsUnit Ginv guard -> all admissible tests. This is the pinned order, not Total order.'
 if s in ('P428Target8Total','p428Target8Total','P428Target8Mixed','p428Target8Mixed','P428Target8Family','p428Target8Family','P428Target8FamilyTorus','p428Target8FamilyTorus'):
  later='c, then m,R,k,Lu,alpha0' if 'Total' in s else ('Phi (and its factor-set condition), then m,R,k,Lu,alpha0' if 'Mixed' in s else ('m,R,k,Lu,alpha0, then F' if 'Torus' in s else 'Fm (and CubeFamOK), then m,R,k,Lu,alpha0'))
  return 'ell>=2, a>0 -> m1>=1, R1, a0>0, gamma0>0 -> '+later+' -> S,Lam,U and test fields. All four constants are uniform over the later data; see §3.1.'
 if s in ('strong_coreT','strong_coreTC','strong_coreTΦ','strong_coreTM'):
  return 'Given the field/operator/right-inverse family proofs and ell,a, choose gamma0,m0,R0,a0 before the factor/family and all m,R,k,Lu,alpha0,S,Lam,U. Internal choices and rescaling: §3.2.'
 if s in ('FieldsKT','fieldsKT_of_ball'):
  return 'ell,a (and the ball-chart family premise for the theorem) -> df,m1,R1,K>=1,C>=1 with C<=K,s>0 -> factor/family, m,R,k,Lu,alpha0,S,Lam,U. Geometry/localization hypotheses are retained.'
 if s in ('ClassFamT','ClassFamTΦ','BallChartsGT','BallChartsT','ballChartsT_of_G','ballChartsGT_proved'):
  return 'ell (and any displayed family premise) -> m1,R1, chart constant C,s>0 -> factor/family,m,R,k,Lu,alpha0,S,Lam,U. General ClassFamT has an arbitrary constant type and Q/P predicates; body supplies the exact order.'
 if s in ('ClassRightInvCovT','classRightInvCovT'):
  return 'ell,a -> m1, cW,cG>=0, R1, s>0 -> factor/family,m,R,k,Lu,alpha0,S,Lam,U -> each source u -> a preimage x. Weighted/covariant-gradient constants are chosen before the class instance (§3.3).'
 if s in ('ClassRightInvT','classRightInvT_of_cov'):
  return 'ell,a -> m1,bN>0,R1,s>0 -> factor/family,m,R,k,Lu,alpha0,S,Lam,U -> source v -> preimage g. The conclusion is an upper-energy extension bound, not a Ginv lower bound (§3.3).'
 if s in ('OpLayerThickT','opLayerThickT_of'):
  return 'ell,a and the displayed chart/right-inverse family proofs -> m1,R1,(theta,KH,KH1,K2,CW,KD),s>0 -> factor/family,m,R,k,Lu,alpha0,S,Lam,U -> column source/centre choices. See §3.3; no all-plaquette response gap.'
 if s in ('fieldsT','fieldsTM','fieldsTQ'):return 'Conjunction of the three preceding family shapes: ell,a -> their constants -> all class data. This theorem discharges the family premises, not selAll premises.'
 if ('patchCoercive' in s and 'exists' in s) or s.startswith('w4_class'):
  return 'ell,a -> cW>0,a0>0,D (and a tail estimate for every d>=D) -> factor/family where present and M,R,k,Lu,S,d,W,U,alpha0,Lam and other displayed analytic premises -> test vector. The actual cwW4 coefficient still needs the numeric lower-bound lemma to be positive.'
 if s in ('cw_uniform','cwW4_lower'):
  return 'cw_uniform: ell,a,epsilon1,epsilon2,m>0 -> delta>0,c>0 -> the numeric perturbation variables. cwW4_lower: all constants/windows and numeric hypotheses are inputs; output is the explicit c lower bound, with no new instance-dependent choice.'
 if 'dlayerObligation' in s or s.startswith('DLayerObligation') or s.startswith('dlayer_explicit'):
  return 'Fix ell,M,R,a,theta,KH,KH1,K2,CW,KD and their hypotheses -> epsilon2s>0,epsilonJ>0 -> positive cap a1 -> k,Lu,alpha0,S,Lam,U and OpLayer -> the two D-layer inequalities. The explicit witness has no k/torus/background dependence (§4c).'
 if s=='a1D' or s=='a1D_pos':return 'Explicit function of ell and fixed operator-layer constants/tolerances only; it is chosen before k,Lu,alpha0,S,Lam,U. Formula in §4c.'
 if s=='dqSmall_exists' or s=='C2full_strat_window':return 'ell>=2 -> a positive smallness window (and its uniform jet coefficient where present) -> the smaller parameter/geometry/background/input quantified in the exact statement. This bounds the jet; it does not make the jet linear in alpha0.'
 if s=='num_RI':return 'ell>=2 -> rho_s>0 -> all 0<=rho<=rho_s; numerical inequalities only. Constants cWR,cGR are explicit functions of ell in RI5.'
 if s in ('rightInv_cfg','classRightInvCov','classRightInv'):
  return 'rightInv_cfg: fix the displayed geometry/chart window and instance, then each u -> a preimage x; cWR,cGR depend only on ell. Family corollaries: follow their ClassRightInv[Cov] binder order (older order may choose R0 after m); do not substitute Total order.'
 if s in ('thin_core_RI','thinTori_RI','p428Target8','p428Target8_of_rightInvCov') or (n.startswith('AdalyFormal.StatementLaneG.') and s=='P428Target8'):
  return 'Older RI6/headline order: ell,a -> m0 -> m>=m0 -> R0 -> R>=R0 -> a0>0,gamma0>0 -> k,Lu,alpha0,S,Lam,U. thin_core_RI has its exact additional premises/packaging below; it is not the Total constant order.'
 if n.startswith('AdalyFormal.D1Residual.') or s in ('P428Target8SG_iff_residualT','P428Target8SG_of_residual','P428Target8SG2'):
  return 'Pointwise bridge: all displayed instance data/units are hypotheses. For GShape/residual/headline statements, ell,a -> m0 -> m -> R0 -> R -> a0 (and gamma0 for an inequality) -> instance/test data -> literal unit guard. Threshold-combination in GShape_imp takes maxima of scale/radius thresholds and a minimum of caps.'
 if s.endswith(('_fromTotal','_fromMixed','_fromFamily')) or '.P428Target8' in n and s.startswith('to'):
  return 'No independently chosen analytic constant: specialization/reordering of the supplied headline. The exact target shape determines which constants precede the factor/family and m,R; never infer a stronger order from the name.'
 if '∃' in h:
  if 'c : PeriodicLatticeSite' in h or ('col' in s or 'L2' in s):return 'All instance data and norm/decay constants are fixed by the hypotheses; for each column source p or e and v, the centre c is chosen afterwards. Not a class-uniform choice of centre or an inverse-response gap.'
  return 'All displayed universal parameters/hypotheses are fixed first; witnesses are chosen only at the existential scope shown in the complete type below. This pointwise conditional result does not independently choose eventual class constants.'
 return 'All displayed constants and instance data are universally supplied (including generalized section parameters in the compiled type); no new class-uniform constants are chosen. Any lower bound, smallness, unit or support premise remains an input.'
def category(d):
 n=d['name'];s=n.split('.')[-1];h=d['header']; out=[]
 if d['kind'] in ('def','abbrev','structure'):return 'Shape/definition (not a proof)'
 if re.search(r'coer|lower|w4_class|W4_nq|cw_uniform|cwW4|\.NE$',n):out.append('(a) lower bound / conditional lower-bound ingredient')
 if re.search('unit|Unit|wellDef|WellDef|rightInv|p428Target|strong_core|thin_core|fieldsT|FieldsK|opLayer',n) or 'IsUnit' in h:out.append('(b) units / class or analytic pipeline')
 if re.search('Delta2|delta2|C2|D2|psi|Jf|J_local|[Dd][Ll]ayer|[Hh]olRegime|DQ|Dg[01]|dparts',n):out.append('(c) correction, raw jet or curvature/source estimate/identity')
 if re.search(r'congr|local|supp|\.inverse$|\.H|H1|col|L2|eq_on|stat_eq',n):out.append('(d) locality, support, decay or conditional inverse comparison')
 return '; '.join(out) if out else 'Supporting compiled algebra/geometry; exact limited scope below'
roots_short={'AdalyFormal.Total.p428Target8Total':'Total','MXP.Total.p428Target8Mixed':'Mixed','MXQ.Total.p428Target8FamilyTorus':'FamilyTorus','AdalyFormal.M2RightInv.p428Target8':'RI6','AdalyFormal.D1Residual.P428Target8SG_iff_pencilT':'guarded equivalence'}
for d in rows:
 d.update(records[d['name']]);d['selector']=selector(d);d['constantOrder']=order(d);d['category']=category(d);d['sourceStatement']=source(d)
(D/'catalog.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
base=(D/'overview.md').read_text()
base+='\n## 6. Verification and inventory scope\n\n'
base+='The catalogue below has **'+str(len(rows))+' individually checked declarations**. Every entry has its source `file:line`, verbatim source signature (or definition body), generalized compiled type, selector scope, constant order, and individual dependency record. Source signatures use their original namespace/open/section context; the adjacent compiled type exposes the generalized section parameters. Lean suppresses only proof-valued arguments as `⋯` in that print; the verbatim source signature retains them. No hypothesis or numerical coefficient was removed from the source signatures.\n\n'
base+='`mine/Trace.lean` imports only frozen modules and traverses the types and values of the five roots named in §2 through project namespaces. It records 15,162 declarations including generated constants; it is a navigation trace, not a proof checker for new claims. It deliberately omits Mathlib/internal namespaces and is not claimed to be a fully closed import/dependency graph. `mine/manifest.json` records which roots reach each inventoried declaration. The inventory filters for the four requested operator/jet topics, includes public neighboring corollaries and exact proposition shapes, and does not promote irrelevant scalar arithmetic, matrix-group units, cutoff derivatives, or toy examples into class-uniform estimates. It is not an assertion that every generic theorem in Mathlib has been enumerated. Nearby results with no root tag are explicitly identified as public neighbors not found in that traced project-namespace closure; import membership alone is never used as proof-dependency evidence. `mine/index.py`, `catalog.py`, `extras.py`, and `report.py` reproduce the inventory (in that order, with the two audit compilations before report generation). The final audit also asks the compiled environment for the originating module of every declaration; all 419 match the quoted source module, avoiding accidental attribution to a same-named fork.\n\n'
base+='Compilation was exclusively through `AHP/round3/lean1.sh`:\n\n- `mine/Trace.lean`: final exit 0, five root dependency records, all permitted.\n- `mine/ChecksV2.lean`: preliminary audit, exit 0, 404 permitted individual dependency records.\n- `mine/ChecksV3.lean`: core audit, exit 0, 406 permitted records and matching source-module origins.\n- `mine/ChecksExtra.lean`: legacy-shape supplement, exit 0, 13 permitted records and matching source-module origins. Final total: 419 distinct declarations. No errors/warnings. These check existing imported declarations, not new proofs.\n- `Attempt.lean`: see `mine/VERIFY.json` for the independently checked exit and exact-pin hash. It is only the unchanged pin, not a solved goal.\n\n'
base+='An earlier `mine/Checks.lean` invocation returned with an empty log and no exit record. It was polled and the process table checked twice: no compiler/wrapper remained. It is not counted as a successful compile and was not launched a second time. The completed expanded catalogue uses distinct `ChecksV2.lean`, `ChecksV3.lean`, and `ChecksExtra.lean` files in persistent terminals. The final core audit waited for the shared heavy slot; no duplicate compile was launched. No numerical script, reproduction, direct Lean/Lake command, build, update, deletion outside this item, commit or push was run. Protected sources and other workers\' files were not edited. One initial search redirection accidentally created `AHP/round4-search.tmp`; it was immediately moved into `guarded/mine/search.txt`, and no file remains at that mistaken path.\n\n'
base+='## 7. Declaration index\n\nUse the full-name search or the source path to locate an entry. **Definitions describe obligations; theorem entries prove only their displayed conclusions.**\n\n| ID | Source | Declaration |\n|---|---|---|\n'
for d in rows:base+=f'| [{d["id"]}](#{d["id"].lower()}) | `{d["file"]}:{d["line"]}` | `{d["name"]}` |\n'
base+='\n## 8. Exact declaration catalogue\n\n'
for d in rows:
 base+=f'<a id="{d["id"].lower()}"></a>\n<details>\n<summary>{d["id"]} — {d["name"]} — {d["file"]}:{d["line"]}</summary>\n\n'
 base+=f'**Kind/category:** {d["kind"]}; {d["category"]}.\n\n**Selector:** {d["selector"]}\n\n**Constant order:** {d["constantOrder"]}\n\n'
 base+='**Trace roots:** '+(', '.join(roots_short[r] for r in d['roots']) or 'Public neighboring declaration; not found in the traced project-namespace closure.')+'.\n\n'
 base+='**Verbatim source '+('definition' if d['kind'] not in ('theorem','lemma') else 'signature')+':**\n\n```lean\n'+d['sourceStatement']+'\n```\n\n'
 base+='**Compiled generalized type:**\n\n```lean\n'+d['type']+'\n```\n\n'
 base+='```text\n'+d['axiomLine']+'\n```\n\n</details>\n\n'
(root/'MINE.md').write_text(base)
print('Wrote',root/'MINE.md',len(base.encode()),'bytes;',len(rows),'declarations')
