# Grepy Remate: count .lean files, lines, theorem/lemma declarations (comments stripped, nested /- -/ aware)
import os, re, sys, collections
root=sys.argv[1]
DECL=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|noncomputable|nonrec|partial|unsafe|scoped)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b')
def strip(text):
    out=[];i=0;depth=0;n=len(text);instr=False
    while i<n:
        if depth==0 and not instr and text.startswith('--',i):
            j=text.find('\n',i); i=n if j<0 else j; continue
        if not instr and text.startswith('/-',i): depth+=1; i+=2; continue
        if depth>0 and text.startswith('-/',i): depth-=1; i+=2; continue
        c=text[i]
        if depth==0:
            if c=='"' and (i==0 or text[i-1]!='\\'): instr=not instr
            out.append(c)
        elif c=='\n': out.append('\n')
        i+=1
    return ''.join(out)
per=collections.OrderedDict(); tot=collections.Counter()
files=[]
for d,_,fs in os.walk(root):
    for f in fs:
        if f.endswith('.lean'): files.append(os.path.join(d,f))
files.sort()
for p in files:
    rel=os.path.relpath(p,root); folder=rel.split('/')[0] if '/' in rel else '(top)'
    t=open(p,encoding='utf-8').read()
    lines=t.count('\n')+(0 if t.endswith('\n') or not t else 1)
    c=collections.Counter(m.group(1) for m in (DECL.match(l) for l in strip(t).split('\n')) if m)
    # naive count (no comment stripping) for comparison
    naive=sum(1 for l in t.split('\n') if re.match(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\b',l))
    e=per.setdefault(folder,collections.Counter()); e['files']+=1; e['lines']+=lines; e['naive']+=naive
    for k,v in c.items(): e[k]+=v
for k,e in per.items():
    tot.update(e)
    print(f"{k:16s} files={e['files']:3d} lines={e['lines']:6d} theorem={e['theorem']:5d} lemma={e['lemma']:5d} def={e['def']:4d} naiveTL={e['naive']}")
print("TOTAL", dict(tot), "theorem+lemma=", tot['theorem']+tot['lemma'])
nt=collections.Counter(); 
for k,e in per.items():
    if k!='(top)': nt.update(e)
print("FOLDERS ONLY", dict(nt), "theorem+lemma=", nt['theorem']+nt['lemma'])
