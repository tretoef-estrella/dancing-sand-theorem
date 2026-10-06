# For the unchanged body (from «1.1 The problem» to «13. Exact status»), compare the multisets of characters of v7 and v8 (whitespace ignored).
import sys, collections
sys.argv = ['x', 'material/paper/THE_DANCING_SAND_THEOREM_v7.pdf', 'material/paper/THE_DANCING_SAND_THEOREM_v8.pdf']
exec(open('scratch/py/wordcmp.py').read().split("a = words(sys.argv[1])")[0])
def body(pdf):
    w = [x for x, _ in words(pdf)]
    def f(seq):
        for i in range(len(w)):
            if w[i:i+len(seq)] == seq: return i
    return w[f(['1.1','The','problem']):f(['13.','Exact','status'])], w[f(['References']):]
for part in (0, 1):
    a = body(sys.argv[1])[part]; b = body(sys.argv[2])[part]
    ca, cb = collections.Counter(''.join(a)), collections.Counter(''.join(b))
    print(['BODY §1.1–§12', 'REFERENCES'][part], 'words', len(a), len(b), 'chars', sum(ca.values()), sum(cb.values()), 'char multisets equal:', ca == cb, 'diff v7-v8:', dict(ca - cb), 'v8-v7:', dict(cb - ca))
