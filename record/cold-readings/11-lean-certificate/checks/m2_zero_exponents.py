# M2 (vacuity of toNat / trivial factors): over every family 1 <= lam <= 1023 and shift 0 <= i <= 12,
# the least pooled big clock and the least small clock; any exponent <= 0 would make a factor trivial.
import sys; sys.path.insert(0, 'checks')
import m2_rule as R
worst = None
for lam in range(1, 1024):
    for i in range(0, 13):
        k, I = R.family(lam)
        if i == 0 and not I:
            continue
        X = R.X(lam, i)
        mn = min(e for e in X if e != 'inf')
        if worst is None or mn < worst[0]: worst = (mn, lam, i)
print('least finite exponent in X(lam, i), 1<=lam<=1023, 0<=i<=12:', worst)
print('rounding of the integer fit acted in:', sorted(set(R.ROUNDING))[:10], 'count', len(set(R.ROUNDING)))
