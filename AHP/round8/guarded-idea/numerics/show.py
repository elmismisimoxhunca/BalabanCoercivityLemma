import json, sys, mpmath as mp
mp.mp.dps = 30
def s(x):
    try: return mp.nstr(mp.mpf(x), 10)
    except Exception: return str(x)
d = json.load(open(sys.argv[1]))
for k, v in d.items():
    if k == 'interval':
        for r in v:
            print('   interval', {kk: ([s(x) for x in vv] if isinstance(vv, list) else s(vv)) for kk, vv in r.items()})
    elif isinstance(v, list):
        print(k, [s(x) for x in v])
    else:
        print(k, s(v))
