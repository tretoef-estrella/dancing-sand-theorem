# Assign every differing run of logs/wordcmp.log to a place of the v8 text, by the headings before it in the v8 word stream.
import re, sys
sys.argv = ['x', 'material/paper/THE_DANCING_SAND_THEOREM_v7.pdf', 'material/paper/THE_DANCING_SAND_THEOREM_v8.pdf']
exec(open('scratch/py/wordcmp.py').read().split("a = words(sys.argv[1])")[0])
b = words(sys.argv[2]); bw = [w for w, _ in b]
def find(seq):
    for i in range(len(bw)):
        if bw[i:i+len(seq)] == seq: return i
    return None
marks = [('header', 0), ('§1.0', find(['1.0','Summary','of','results'])), ('§1.1+', find(['1.1','The','problem'])),
         ('§13', find(['13.','Exact','status'])), ('after §13 bullets', find(['No','human','expert','has','refereed','any'])),
         ('Acknowledgements', find(['Acknowledgements'])), ('Appendix A', find(['Appendix','A.','How'])), ('References', find(['References']))]
print(marks)
for line in open('logs/wordcmp.log'):
    m = re.match(r'--- (\w+) v7 p\.(\d+) words (\d+)-(\d+) \((\d+)\) \| v8 p\.(\d+) words (\d+)-(\d+)', line)
    if not m: continue
    b1 = int(m.group(7)); place = [n for n, pos in marks if pos is not None and pos <= b1][-1]
    print(f'{place:20s} v8 p.{m.group(6):>2s} word {b1:6d}  {m.group(1)} -{m.group(5)}')
