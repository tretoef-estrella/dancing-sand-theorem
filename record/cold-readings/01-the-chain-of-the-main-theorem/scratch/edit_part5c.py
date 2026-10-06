# -*- coding: utf-8 -*-
p = 'REPORT_COLD.md'
s = open(p, encoding='utf-8').read()
old7 = "## 7. My errors\n"
assert old7 in s
s = s.replace(old7, """**Failures, in the same size of type:** none of my sealed predictions failed. One sealed scope was not met (C4b at λ = 30: i ≤ 12 instead of i ≤ 64). That every prediction held is itself a warning: most were predictions that the flights' claims survive my checks, at odds 90–99 %, so they could not surprise me much; the controls (each of which fired) are what show the checks could fail. Two checks are blind to the big-clock rule by construction (Bai's two counts), and one control (carries at m) is invisible to Gao et al.'s theorems; I said so when sealing or when reporting.

""" + old7)
open(p, 'w', encoding='utf-8').write(s)
print('ok')
