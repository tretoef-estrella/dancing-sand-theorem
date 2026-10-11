# Grepy Cotejo: the folded cube of v9 §1.3 against the Cayley graph and Lean's lapBar, n = 1..9
from collections import Counter
for n in range(1, 10):
    N = 1 << n; one = N - 1
    cls = lambda x: min(x, x ^ one)
    V = sorted(set(cls(x) for x in range(N)))
    # v9 description: {x,x+1} joined to {x+e_i, x+1+e_i} once for each i (an edge is an unordered pair with its label i)
    E = set()
    for c in V:
        for i in range(n):
            E.add((frozenset((c, cls(c ^ (1 << i)))), i))
    # preimages in Q_n
    pre = Counter()
    for x in range(N):
        for i in range(n):
            y = x ^ (1 << i)
            if x < y: pre[(frozenset((cls(x), cls(y))), i)] += 1
    assert set(pre) == E
    precount = Counter(pre.values())
    loops = sum(1 for (e, i) in E if len(e) == 1)
    # Laplacian of the multigraph (loops do not count) vs lapBar: n*u(x) - sum_i u(x + mk e_i)
    idx = {c: k for k, c in enumerate(V)}; m = len(V)
    Lg = [[0]*m for _ in range(m)]
    for (e, i) in E:
        if len(e) == 2:
            a, b = tuple(e); Lg[idx[a]][idx[a]] += 1; Lg[idx[b]][idx[b]] += 1; Lg[idx[a]][idx[b]] -= 1; Lg[idx[b]][idx[a]] -= 1
    Lb = [[0]*m for _ in range(m)]
    for c in V:
        Lb[idx[c]][idx[c]] += n
        for i in range(n): Lb[idx[c]][idx[cls(c ^ (1 << i))]] -= 1
    same = Lg == Lb
    # simple and regular?
    mult = Counter(e for (e, i) in E)
    simple = loops == 0 and max(mult.values()) == 1
    deg = Counter()
    for (e, i) in E:
        for v in e: deg[v] += (2 if len(e) == 1 else 1)
    # v8 literal reading: number of word pairs, one from each class, differing in one letter
    lit = Counter()
    for a in V:
        for b in V:
            if a < b:
                k = sum(1 for x in (a, a ^ one) for y in (b, b ^ one) if bin(x ^ y).count('1') == 1)
                if k: lit[k] += 1
    print(f'n={n}: vertices={m} (2^(n-1)={N//2}) edges={len(E)} loops={loops} preimage-counts={dict(precount)} '
          f'Laplacian==lapBar:{same} simple={simple} degrees={sorted(set(deg.values()))} '
          f'max multiplicity={max(mult.values())} v8-literal pair counts={dict(lit)}')
