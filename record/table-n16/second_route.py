# Second route for the table of §1.9 (n = 2..16): the first cold reader's own rule engine
# (record/cold-readings/01-the-chain-of-the-main-theorem/engines/myrule.py, written without our code), forms B and X,
# against the rule log paper_rule_abs_2_16.log (the paper's gate/rule_abs.py). Run from this folder.
import sys, re, ast, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '..', 'cold-readings', '01-the-chain-of-the-main-theorem', 'engines'))
import myrule
ours = {}
for l in open(os.path.join(here, 'paper_rule_abs_2_16.log')):
    m = re.match(r'(\d+) (\{.*\})', l)
    if m: ours[int(m.group(1))] = ast.literal_eval(m.group(2))
def strip(G):  # remove the summand Z_2 of the Main Theorem's left side
    G = dict(G); assert G.pop('Z', 1) == 1; return {e: c for e, c in G.items() if c}
bad = 0
for n in range(2, 17):
    for form in ('B', 'X'):
        G = strip(myrule.group_rule(n, form=form)); ok = G == ours[n]; bad += not ok
        print(n, form, 'MATCH' if ok else 'DIFF', '' if ok else G)
ctl = sum(strip(myrule.group_rule(n, form='B', pool=False)) != ours[n] for n in range(2, 17))
print('control (no pooling) rows differing:', ctl, '(must be > 0)')
print('END bad =', bad)
