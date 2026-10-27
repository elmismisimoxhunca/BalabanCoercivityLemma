#!/usr/bin/env python3
"""Audit the round-15 seed R1 source, compilation, and numerical exit records."""
from pathlib import Path
import hashlib,json,re
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[3]
MAIN=OUT/'Seed.lean'
SHARED=ROOT/'AHP/round15/shared/seed/R1_Seed.lean'
NEW=[
 'ChargedLeadingMatrix','radiusChargedObservable',
 'radiusDominantData_of_chargedLeadingMatrix','ChargedLeadingData',
 'DyadicChargedLeadingCertificate','cofinalUnitDominantAreaSeed_of_chargedLeading',
 'q10','q18','candidateH','candidateH_factor','q10_eq_transform',
 'dominantY','dominantDisc','dominantRho','dominantY_gt_two','dominantDisc_eq',
 'dominantDisc_pos','dominantRho_pos','dominantRho_inv','dominantRho_add_inv',
 'dominantRho_lt_one','dominantRho_quartic','fixedMatrix','fixedSeed',
 'fixedLeadingConstant','fixedLeadingConstant_ne_zero','fixedSeed_ne_zero']
FORBIDDEN=re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)\b')
PERMITTED={'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    checks={}
    checks['publication_byte_identity']=MAIN.read_bytes()==SHARED.read_bytes()
    checks['source_has_no_forbidden_mechanism']=not FORBIDDEN.search(MAIN.read_text())
    for p in [MAIN,SHARED,OUT/'collar_probe.py',OUT/'analyze_transfer.py']:
        exit_path=Path(str(p)+'.exit') if p.suffix=='.lean' else p.with_suffix('.exit')
        checks[f'exit_zero:{p.name}']=exit_path.exists() and exit_path.read_text().strip()=='0'
    for p in [MAIN,SHARED]:
        log=Path(str(p)+'.log').read_text()
        checks[f'clean_log:{p.name}']=not re.search(r'error|warning|sorryAx',log)
        for name in NEW:
            full=f'AdalyFormal.Round15.Seed.{name}'
            m=re.search(re.escape("'"+full+"' depends on axioms:")+r'\s*\[([^]]*)\]',log,re.S)
            assert m, f'missing axiom record {full} in {p}'
            axioms={x.strip() for x in m.group(1).split(',')}
            assert axioms<=PERMITTED,(full,axioms)
        checks[f'all_new_axiom_records_permitted:{p.name}']=True
    result={'pass':all(checks.values()),'checks':checks,
      'source':str(MAIN.relative_to(ROOT)),'shared':str(SHARED.relative_to(ROOT)),
      'source_sha256':sha(MAIN),'shared_sha256':sha(SHARED),
      'source_lines':len(MAIN.read_text().splitlines()),
      'new_declarations_checked':NEW,
      'qualification':'Conditional charged-leading interface and exact candidate algebra only; no physical area-seed proof.'}
    (OUT/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    assert result['pass']
if __name__=='__main__': main()
