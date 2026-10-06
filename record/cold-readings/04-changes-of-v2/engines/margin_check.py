# margin_check.py — Grepy el lector frío del cubo 4: words beyond the right margin (pdftotext -bbox output).
import re, sys, collections
html = open(sys.argv[1]).read()
pages = html.split('<page ')[1:]
allmax = []
for pn, pg in enumerate(pages, 1):
    W = float(re.search(r'width="([\d.]+)"', pg).group(1))
    xs = [(float(m.group(3)), m.group(5)) for m in re.finditer(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">(.*?)</word>', pg)]
    if not xs: continue
    mx = max(x for x, _ in xs)
    allmax.append(mx)
    cnt = collections.Counter(round(x) for x, _ in xs)
    print(f"page {pn:2d}: width {W:.0f}, max xMax {mx:.1f}, word at max: {max(xs)[1][:30]!r}")
allmax.sort()
print("median of page maxima:", allmax[len(allmax)//2], " overall max:", allmax[-1])
