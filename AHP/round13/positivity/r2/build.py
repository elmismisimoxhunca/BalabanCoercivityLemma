from pathlib import Path
import hashlib,json,argparse
root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--publish',action='store_true')
args=parser.parse_args()
copies=[]
def take(file,start,end):
    text=''.join(Path(file).read_text().splitlines(True)[start-1:end])
    copies.append(dict(source=file,start=start,end=end,sha256=hashlib.sha256(text.encode()).hexdigest()))
    return text
prefix=take('AHP/round13/positivity/r1/MassAbsorption.lean',1,1058)+'\n'+take('AHP/round13/positivity/r1/EightLeaves.lean',8,693)+'\n'+take('AHP/round13/positivity/r1/EightLeaves.lean',780,914)+'\n'
body=(root/'Geometry.lean.txt').read_text()+'\n'+(root/'Estimates.lean.txt').read_text()+'\n'+(root/'Arms.lean.txt').read_text()+'\n'+(root/'Sum.lean.txt').read_text()
(root/'StarGeometry.lean').write_text(prefix+body)
flat=take('AHP/round13/positivity/r1/LocalPositive.lean',230,1096)+'\n'+take('AHP/round13/positivity/r1/LocalPositive.lean',1409,1472)+'\n'
interfaces=take('AHP/round12/shared/kernel/R2_FirstCrossing.lean',975,993)+'\n'
interfaces+='namespace AdalyFormal.Round12.Kernel.Actual\nopen AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane\nopen AdalyFormal.Round4.Guarded.RefuteR1\nopen AdalyFormal.Round9.Guarded.AnalyticR1\nopen AdalyFormal.Balaban.CovariantOperators (BondFnL2)\nopen AdalyFormal.Balaban.AdmissibleSubspace (Bond)\n'
interfaces+=take('AHP/round12/shared/kernel/R2_FirstCrossing.lean',1670,1677)+'\nend AdalyFormal.Round12.Kernel.Actual\n'
(root/'P2.lean').write_text(prefix+body+'\n'+flat+interfaces+'\n'+(root/'Join.lean.txt').read_text())
(root/'COPIES.json').write_text(json.dumps(copies,indent=2)+'\n')
if args.publish:
    shared=Path('AHP/round13/shared/positivity')
    shared.mkdir(parents=True,exist_ok=True)
    for name in ['StarGeometry','P2']:
        (shared/f'R2_{name}.lean').write_bytes((root/f'{name}.lean').read_bytes())
