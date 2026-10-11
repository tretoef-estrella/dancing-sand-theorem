import sys
p=sys.argv[1]; s=open(p).read()
s=s.replace('</style>','p:has(+ table){break-after:avoid;page-break-after:avoid} tr{break-inside:avoid} a{color:#1a4a8a;text-decoration:none}</style>',1)
s=s.replace('<meta charset="utf-8">','<meta charset="utf-8"><meta name="author" content="Rafael Amichis Luengo">',1)
import re
def keep(m):
    t=re.sub(r'<[^>]+>','',m.group(0))
    return m.group(0).replace('<p>','<p class="keep">',1) if len(t)<420 else m.group(0)
s,n=re.subn(r'<p><em>Proof\.</em>.*?</p>',keep,s,flags=re.S)
s=s.replace('</style>','p.keep{break-inside:avoid;page-break-inside:avoid} .display:has(+ .display){break-after:avoid;page-break-after:avoid}</style>',1)
def aft(m):   # (67) v6: a one-line paragraph after a display or a list stays with it (no widow at the top of a page)
    t=re.sub(r'<[^>]+>','',m.group(2))
    return m.group(1)+('<p class="aft">' if len(t)<100 else '<p>')+m.group(2)+'</p>'
s,na=re.subn(r'(</div>\n|</ul>|</ol>)<p>(.*?)</p>',aft,s,flags=re.S)
s=s.replace('</style>','p.aft{break-before:avoid;page-break-before:avoid}</style>',1)
print('short paragraphs kept after a display or list:',s.count('class="aft"'))
print('short proofs kept together:',s.count('class="keep"'),'of',n)
open(p,'w').write(s)
