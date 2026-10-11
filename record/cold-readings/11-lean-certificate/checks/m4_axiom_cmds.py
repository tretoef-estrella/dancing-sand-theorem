# M4: per piece, number of `#print axioms` commands in project/checks/CheckC<p>.lean versus number of
# axiom lines in its final log; and whether every theorem named in the .lean appears in the log.
import os, re
M = 'material'; PP = f'{M}/logs/per_piece'; CK = f'{M}/project/checks'
pieces = sorted({f.split('_')[0] for f in os.listdir(f'{M}/pieces') if f.endswith('.md')}, key=lambda s: (int(re.match(r'C(\d+)', s).group(1)), s))
tot_cmd = tot_log = 0; diffs = []
for p in pieces:
    lf = 'checkC31b.log' if p == 'C31' else [f for f in os.listdir(PP) if f.lower() == f'check{p.lower()}.log'][0]
    src = open(f'{CK}/Check{p}.lean', encoding='utf-8').read()
    src_nc = re.sub(r'/-.*?-/', '', src, flags=re.S); src_nc = re.sub(r'--[^\n]*', '', src_nc)
    cmds = re.findall(r'#print axioms\s+(\S+)', src_nc)
    log = open(f'{PP}/{lf}', encoding='utf-8').read()
    names = re.findall(r"^'(.+?)' (?:depends on axioms|does not depend)", log, re.M)
    tot_cmd += len(cmds); tot_log += len(names)
    if len(cmds) != len(names): diffs.append((p, len(cmds), len(names)))
print('#print axioms commands in the 68 CheckC*.lean (comments removed):', tot_cmd, '; outputs in the 68 final logs:', tot_log)
print('pieces where the two differ:', diffs)
