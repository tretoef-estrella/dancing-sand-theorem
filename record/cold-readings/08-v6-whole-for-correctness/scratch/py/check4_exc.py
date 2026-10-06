# replicate check 4 of acceptance.py on a bbox file and print every page whose top line is short and ends a sentence,
# marking where the statement-label exception (and the left-edge condition) decide
import re,html,sys
B=open(sys.argv[1]).read()
for pi,p in enumerate(B.split('<page ')[1:],1):
    ws=[(float(a),float(b),float(c),float(d),html.unescape(w)) for a,b,c,d,w in re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>',p)]
    ws=[w for w in ws if w[3]-w[1]>=12]
    if not ws or pi==1: continue
    top=min(w[1] for w in ws)
    line=sorted([w for w in ws if abs(w[1]-top)<3],key=lambda w:w[0])
    qed=any(w[4]=='∎' for w in line)
    line=[w for w in line if w[4]!='∎'] or line
    width=max(w[2] for w in line)-min(w[0] for w in line)
    text=' '.join(w[4] for w in line)
    label=re.match(r'(Lemma|Theorem|Proposition|Corollary|Definition|Remark)s? [0-9.]+',text)
    short=width<0.6*488; ends=bool(qed or re.search(r'[.:;]$',text)); left=min(w[0] for w in line)<70
    flag=short and ends and left
    if short or label: print(f'p{pi}: width {width:.0f} short={short} ends={ends} left={left} label={bool(label)} WIDOW={flag and not label} | {text[:90]}')
