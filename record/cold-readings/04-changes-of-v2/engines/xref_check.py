# xref_check.py — Grepy el lector frío del cubo 4, 2026-10-05. Cross-references of the v2 text.
import re, sys
txt = open(sys.argv[1]).read()
lines = txt.split("\n")
kinds = r"(Lemma|Theorem|Proposition|Corollary|Remark|Remarks)"
defs = {}
for n, L in enumerate(lines, 1):
    for m in re.finditer(r"\*\*" + kinds + r" (\d+\.\d+)", L):
        defs.setdefault((m.group(1), m.group(2)), n)
    for m in re.finditer(r"> \*\*" + kinds + r" (\d+\.\d+)", L):
        defs.setdefault((m.group(1), m.group(2)), n)
secs = set()
for L in lines:
    m = re.match(r"#{2,3} (\d+(\.\d+)?)\.? ", L)
    if m: secs.add(m.group(1))
labels = {num for (_, num) in defs}
print("defined labels:", len(defs))
bad = 0
for n, L in enumerate(lines, 1):
    for m in re.finditer(kinds + r"s? (\d+\.\d+)((?:[–\-, ]+(?:and )?\d+\.\d+)*)", L):
        k, num, rest = m.group(1), m.group(2), m.group(3)
        nums = [num] + re.findall(r"\d+\.\d+", rest)
        kk = k.rstrip("s") if k != "Remarks" else "Remarks"
        for x in nums:
            if (kk, x) not in defs:
                # a range like 9.7–9.9 lists endpoints only
                print(f"  line {n}: reference {kk} {x} has no definition with that kind;", "label exists as" , [d for d in defs if d[1]==x])
                bad += 1
    for m in re.finditer(r"§(\d+(?:\.\d+)?)", L):
        if m.group(1) not in secs:
            print(f"  line {n}: section §{m.group(1)} not found"); bad += 1
print("sections:", sorted(secs, key=lambda s: [int(t) for t in s.split('.')]))
print("problems:", bad)
