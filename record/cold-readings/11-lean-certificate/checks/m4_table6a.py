# M4: Table 6a (brute force) against logs/brute_force/chkC<p>.log: number of checks, failures, controls.
import os, re
M = 'material'; BF = f'{M}/logs/brute_force'
cert = open(f'{M}/certificate/LEAN_CERTIFICATE_DANCING_SAND_v1.md').read().replace(' ', ' ')
sec = cert.split('**Table 6a.')[1].split('**Table 6b.')[0]
rows = {}
for line in sec.splitlines():
    m = re.match(r'\| (C\w+) \| `(\w+)` \| ([^|]+) \| `(\w+)` \| ([^|]+) \| ([^|]+) \|', line)
    if m: rows[m.group(1)] = m.group(6).strip()
print('Table 6a rows:', len(rows))
for p, bf in rows.items():
    log = open(f'{BF}/chk{p}.log', encoding='utf-8', errors='replace').read()
    last = log.rstrip().splitlines()[-1]
    t = log.lower()
    # failures
    fails = re.findall(r'(?:failures|fails)[:= ]+(\d+)', t)
    # check counts
    cnt = re.findall(r'(\d[\d ]*) checks', t) + re.findall(r'checks[:= ]+(\d+)', t)
    cnt = [int(c.replace(' ', '')) for c in cnt]
    # controls
    ctl = re.findall(r'controls?(?: fired)?[: ]+(\d+)\s*(?:/|of)\s*(\d+)', t)
    fire_flags = len(re.findall(r'controls fire: true|controls-fire|all fire', t))
    m_c = re.search(r'([\d ]+) checks', bf); claimed_cnt = int(m_c.group(1).replace(' ', '')) if m_c else None
    m_k = re.search(r'controls (\d+)/(\d+)', bf); claimed_ctl = (int(m_k.group(1)), int(m_k.group(2))) if m_k else None
    ok_cnt = claimed_cnt is None or claimed_cnt in cnt
    ok_fail = bool(fails) and all(f == '0' for f in fails)
    ok_ctl = claimed_ctl is not None and ((str(claimed_ctl[0]), str(claimed_ctl[1])) in ctl or (claimed_ctl[0] == claimed_ctl[1] and fire_flags > 0))
    flag = '' if (ok_cnt and ok_fail and ok_ctl and 'exit=0' in last) else '   <-- look'
    print(f'{p:5s} table: {bf:45s} | log: checks {cnt[:3]} fails {fails[:3]} controls {ctl[:2]} fireflags {fire_flags} | {last[:40]}{flag}')
