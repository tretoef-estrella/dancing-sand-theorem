# head_vs_jump.py — cold reader 5. Where does the head of the fit sit relative to the jumps of the penalty shift?
import sys
sys.argv = ['x']
src = open('checks/gate_cold5.py').read().split('def main')[0]
exec(src)
LAMMAX, IMAX = 255, 40
n = 0; reach = 0; ex = []
hist = {}
for lam in range(1, LAMMAX + 1):
    k, I = family(lam); K = 1 << k
    o = dancers(I); N = len(o)
    for i in range(1, IMAX + 1):
        m = i - 1; ell = m % K
        xH, J = house(I, k, ell, 1)
        Pr, Pc = v2((m >> k) + 1), v2(((m + K) >> k) + 1)
        b = boundary(J)
        if b is None or (Pr == 0 and Pc == 0): continue
        sh = [-Pr * J[p] + Pc * J[N - 1 - p] for p in range(N)]
        y = [xH[p] + sh[p] for p in range(N)]
        head = pav(y)[0][1]
        jump = min(b, N - b)
        n += 1
        key = (head < jump, head == jump, head > jump)
        hist[key] = hist.get(key, 0) + 1
        if head >= jump:
            reach += 1
            if len(ex) < 5: ex.append((lam, i, N, b, head, Pr, Pc))
print(f"cells {n}; head reaches a jump in {reach}; histogram (head<jump, head==jump, head>jump): {hist}; examples (lam,i,N,b,head,Pr,Pc): {ex}")
print("FIN-OK")
