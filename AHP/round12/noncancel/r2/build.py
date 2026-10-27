#!/usr/bin/env python3
"""Build compact R2 publications; no compiler or earlier-round writes."""
from pathlib import Path
import subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
subprocess.run([sys.executable,str(HERE/'build_family.py')],check=True)
(HERE/'FullPlaquette.lean').write_text((ROOT/'AHP/round12/noncancel/r1/Plaquette.lean').read_text()+
    (HERE/'FullPlaquetteAppendix.lean.txt').read_text())
parts=['FullPlaquette','Boundary','Mass','RightFamily']
text=(HERE/(parts[0]+'.lean')).read_text()
for part in parts[1:]:
    s=(HERE/(part+'.lean')).read_text()
    assert s.startswith('import DrEquiv\n')
    text+='\n'+s.removeprefix('import DrEquiv\n')
(HERE/'Attempt.lean').write_text(text)
if '--publish' in sys.argv:
    dest=ROOT/'AHP/round12/shared/noncancel'
    for local,pub in [('Boundary','R2_Boundary'),('FullPlaquette','R2_FullPlaquette'),
                       ('Mass','R2_Mass'),('RightFamily','R2_RightFamily'),('Attempt','R2_StarLocal')]:
        (dest/(pub+'.lean')).write_bytes((HERE/(local+'.lean')).read_bytes())
print('Attempt.lean',len(text.splitlines()),'lines; goal remains open')
