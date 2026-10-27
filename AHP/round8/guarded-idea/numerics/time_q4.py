import sys, time
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/sebastian/BalabanCoercivityLemma/AHP/round6/probe')
from probe import *
import resource
resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))
from scipy.linalg import eigvalsh
mp.mp.dps = 20
t0 = time.time()
f = Family(4, 18, mp.mpf(0), 15, 15, 1).assemble()
t1 = time.time()
lu = splu(f.aug.scipy()); rhs = np.zeros((f.aug.n, len(f.boundary)), complex)
rhs[f.boundary, np.arange(len(f.boundary))] = 1
X = lu.solve(rhs); C = X[f.boundary]; S = np.linalg.inv(C); S = (S + S.conj().T) / 2
th0 = np.array(f.theta(0).tolist(), complex); th1 = np.array(f.theta(mp.pi/2).tolist(), complex)
t2 = time.time()
for t in [0.55, 0.5593, 0.56]:
    print(t, eigvalsh(S + np.cos(t)*th0 + np.sin(t)*th1)[:3])
print('assembly', t1 - t0, 's; LU+schur', t2 - t1, 's; n', f.n, 'aug', f.aug.n, 'rss MB', resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024)
