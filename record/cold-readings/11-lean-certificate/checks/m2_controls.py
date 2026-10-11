# M2 negative controls: deliberately wrong variants of the rule must disagree with the Smith forms.
import json, sys
sys.path.insert(0, 'checks')
import m2_rule as R
S = json.load(open('checks/m2_smith_out_big.json'))
def count_fail():
    bad = 0
    for n_s, res in S.items():
        n = int(n_s); R.X.__globals__  # noqa
        if R.norm(R.rhs(n)) != res['cube']['2']: bad += 1
    return bad
orig_fit, orig_clock, orig_family = R.int_antitonic_fit, R.raw_clock, R.family
variants = {
 'no pooling': lambda: setattr(R, 'int_antitonic_fit', lambda x: (list(x), False)),
 'floors first in the integer fit': None,
 'kappa(i+o_D, xi) without -1': lambda: setattr(R, 'raw_clock', lambda lam, i, D, I, k: orig_clock(lam, i + 1, D, I, k) if True else 0),
 'digits of lambda (not lambda+1)': lambda: setattr(R, 'family', lambda lam: orig_family(lam - 1) if lam >= 1 else orig_family(0)),
 'no h(D) term': lambda: setattr(R, 'raw_clock', lambda lam, i, D, I, k: orig_clock(lam, i, D, I, k) - sum(R.nxt(t, I, k) - t for t in D)),
}
def fit_floor_first(x):
    y, ra = orig_fit(x); return y, ra
for name, setup in variants.items():
    R.int_antitonic_fit, R.raw_clock, R.family = orig_fit, orig_clock, orig_family
    if setup is None:
        print(name, ': not testable (the rounding never acts, see m2_rule.log)'); continue
    setup()
    try:
        b = count_fail()
    except AssertionError as e:
        b = 'assertion'
    print(f'{name}: dimensions n=1..11 where the variant disagrees with the Smith form: {b}')
R.int_antitonic_fit, R.raw_clock, R.family = orig_fit, orig_clock, orig_family
print('original rule disagreements:', count_fail())
