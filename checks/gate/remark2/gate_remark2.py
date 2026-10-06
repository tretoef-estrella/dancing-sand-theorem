# gate_remark2.py — the measurements behind Remark (2) of §10.5 of «The Dancing Sand Theorem» (v2).
# Run from this folder:  python3 gate_remark2.py KIND WEIGHTS SEED     (the paper uses SEED = 11)
#   KIND    = generic : payments 4 q(d), q(d) random in [-9, 9] (a draw 0 is replaced by 1), coefficient of F equal to 1
#             oddU    : payments 4(d + c), coefficient of F a random odd u(d) in [-17, 19] depending on the floor
#   WEIGHTS = rand    : constant random integer coefficients zeta_m in [-5, 5] of F^(m), m >= 2
#             eta     : the coefficients eta_m of Psi_0 (§10.2) instead; the random stream is kept aligned
# alpha = 2, the lattices T(l), l = 2..63, shifts c = 1..4: 248 dances. «clean» counts the dances in which every move is clean.
# engines/ holds three files of the project's flight 9 (fdance.py, tilt_dp.py, g9_explore.py), copied unchanged.
import sys
sys.path.insert(0, 'engines'); sys.dont_write_bytecode = True
import g9_explore as g
kind, setup, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
assert kind in ('generic', 'oddU') and setup in ('rand', 'eta')
if setup == 'eta':
    orig = g.weights
    def w(k, mmax, rnd=None):
        if k == 'rand':
            if rnd is not None:
                for _ in range(mmax - 1): rnd.randint(-5, 5)   # keep the random stream aligned
            return orig('tanh', mmax)
        return orig(k, mmax, rnd)
    g.weights = w
g.e2(63, kind, 2, seed=seed)
