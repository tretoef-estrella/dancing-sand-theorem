# Compare Lean's #eval of the raw clocks (checks/L2_clocks_podium.log) with the Python clocks from the paper.
import ast
log = open('checks/L2_clocks_podium.log').read()
line = [l for l in log.splitlines() if l.startswith('[[')][0]
lean = ast.literal_eval(line)
py = ast.literal_eval(open('checks/m2_clocks_py.txt').read())
n = sum(len(x) for fam in py for x in fam)
print('families', len(lean), len(py), 'clock values', n, 'identical:', lean == py)
