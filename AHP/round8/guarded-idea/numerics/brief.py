import json, sys
import mpmath as mp
mp.mp.dps = 1200
def s(x):
    if isinstance(x, str):
        try:
            return mp.nstr(mp.mpf(x), 11, min_fixed=0, max_fixed=0)
        except Exception:
            return x
    return x
for fn in sys.argv[1:]:
    d = json.load(open(fn))
    print('==', fn.split('/')[-1])
    for k in ['tC1_minus_tB1', 'tB2_minus_tB1', 'tC2_minus_tB1', 'A_boundary_spectrum_at_tC1', 'C_boundary_spectrum_at_tC1',
              'A_negative_count_at_tC1', 'A_boundary_spectrum_at_tB1', 'C_boundary_spectrum_at_tB1', 'A_boundary_min_at_0', 'C_boundary_min_at_0',
              'unit_kernel_pairing', 'first_order_ratio', 'corrected_kernel_augmented_residual', 'exterior_pencil_identity_error', 'seconds', 'peak_rss_KiB']:
        v = d.get(k)
        print('  ', k, [s(x) for x in v] if isinstance(v, list) else s(v))
    for r in d.get('interval', []):
        print('   interval', s(r['t_minus_tB1']), 'A', [s(x) for x in r['A_low'][:2]], 'C', [s(x) for x in r['C_low'][:2]], 'negA', r['A_negative'], 'negC', r['C_negative'])
