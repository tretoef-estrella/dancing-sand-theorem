import subprocess,re,difflib,sys
def pdfwords(p):
    t=subprocess.run(['pdftotext','-layout',p,'-'],capture_output=True,text=True).stdout
    lines=[l for l in t.split('\n') if not re.fullmatch(r'\s*\d{1,3}\s*',l)]
    return ' '.join(lines).split()
def mdwords(p): return open(p,encoding='utf-8').read().split()
def changes(a,b):
    sm=difflib.SequenceMatcher(None,a,b,autojunk=False); out=[]
    for op,i1,i2,j1,j2 in sm.get_opcodes():
        if op!='equal': out.append((op,' '.join(a[i1:i2]),' '.join(b[j1:j2])))
    return out
P='material/paper/THE_DANCING_SAND_THEOREM_'
pa,pb=pdfwords(P+'v9.pdf'),pdfwords(P+'v10.pdf')
ma,mb=mdwords(P+'v9.md'),mdwords(P+'v10.md')
pc=changes(pa,pb); mc=changes(ma,mb)
print('pdf word changes:',len(pc)); 
for c in pc: print('  PDF',c[0],'|-',c[1][:150],'|+',c[2][:150])
print('md word changes:',len(mc))
for c in mc: print('  MD ',c[0],'|-',c[1][:150],'|+',c[2][:150])
# total words removed/added
strip=lambda s: re.sub(r'[`*_\[\]()]','',s)
print('pdf removed words',sum(len(c[1].split()) for c in pc),'added',sum(len(c[2].split()) for c in pc))
print('md  removed words',sum(len(c[1].split()) for c in mc),'added',sum(len(c[2].split()) for c in mc))
