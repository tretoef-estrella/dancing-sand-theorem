# Version 8 of «The Dancing Sand Theorem»: the static record (ARRANQUE_GREPY_ESCRIBANO_v1 §3, step 2).
# Edits only five places: header, §1.0 paragraph, §13 bullets, Acknowledgements sentence, Appendix A entries 3-7.
# Every replacement is asserted unique. Every clause was checked against reports and gradings 3-9 (see CORRECTIONS_v7_to_v8.md).
import re, sys
P = 'scratch/te_v8.md'
s = open(P, encoding='utf-8').read()

def rep(old, new, label):
    global s
    n = s.count(old)
    assert n == 1, (label, n)
    s = s.replace(old, new, 1)
    print('ok', label)

# 1. header
rep('6 October 2026 · version 7', '6 October 2026 · version 8', 'header')

# 2. §1.0 paragraph
i = s.index('Every proof behind the table was re-derived')
j = s.index('\n', i)
old = s[i:j]
assert old.endswith('what we found in the literature, and where we searched, is in §1.8.'), 'para end'
new = ('Every proof behind the table was re-derived by a reader other than its author. '
 'The chains of the Main Theorem and of Theorem DW were read cold before this text was written, by readers with no access to the audits. '
 'The first version of this text was read cold as a whole on 5 October 2026 by a reader with no access to the constructors\' reports, the audits or the earlier readings: «holds with gaps». '
 'It found one gap: the integer part of Lemma 7.2(b) was false as stated, and four proofs used it; no theorem was affected. '
 'The second version repaired it (§7.1, §7.4, §7.5, §9.2), and its changes were read cold the same day by another reader: **the repair holds**. '
 'That reader also found one false sentence, in a remark used nowhere (the author then found the same missing hypothesis in Lemma 10.6(a), harmless because its only use is for an even system), '
 'and found, with a two-line proof, that the fit of every house is integral (Lemma 7.9). '
 'The changes of each later version were read cold in turn, each time by a new reader; none of these readings found a gap or an error in the mathematics. '
 'Between them, they found false or inexact sentences in the record of the work and in §12, points of presentation, and defects of typesetting; '
 'what was corrected, and what was left as it was, is listed with its source in the record kept with the project (Appendix A). '
 'No human expert has refereed this work. '
 'The words of our own are translated into standard terms in §1.7; what we found in the literature, and where we searched, is in §1.8.')
rep(old, new, '§1.0')

# 3. §13 bullets (closing paragraph kept)
i = s.index('## 13. Exact status\n\n') + len('## 13. Exact status\n\n')
j = s.index('\n\nNo human expert has refereed any part of this work.', i)
old = s[i:j]
assert old.startswith('- **Proved, with the grade') and old.rstrip().endswith('a human referee; a formal verification.'), '§13 bounds'
new = '\n'.join([
 '- **Proved, with the grade «pencil, audited, read cold»:** the Main Theorem; Theorem D; Theorems O and F; Theorem DW and Corollary 1.4; Corollaries 1.5, 1.6 and 1.7. Their proofs were read cold as text in the first version of this text, which had one gap (Lemma 7.2(b)); the repair was read cold in its turn, and so were the changes of every later version (Appendix A).',
 '- **Added in version 3, audited, read cold:** Lemma 7.9 in its new form (integrality of the fit), found and proved by the fourth reader, re-proved by the auditor, and re-derived by the fifth reader.',
 '- **Numbered statements changed after the first version:** version 2 restated Lemma 7.2(b) and added the strictness of the cuts to the (Cut) of Theorem 7.8; version 3 strengthened Lemma 7.9, added the hypothesis «even» to Lemma 10.6(a), and added the explicit quantifier «for every `L ≥ 0` and every floor `f`» to Lemma 10.10. No other numbered statement changed in what it states; numbers, notation and typesetting changed.',
 '- **Measured, not proved:** the turned lid (§11, question 2), and the measurements of Remark (2) of §10.5.',
 '- **Not done:** a human referee; a formal verification.'])
rep(old, new, '§13')

# 4. Acknowledgements
rep('The work took five days, from 2 to 6 October 2026. It began on 2 October 2026 as a search',
    'The work began on 2 October 2026 as a search', 'acknowledgements')

# 5. Appendix A: entries «Version 3» to «Version 7» -> «Later versions»
i = s.index('\n- **Version 3** states that integrality as Lemma 7.9') + 1
j = s.index('**Its changes have not yet been read cold.**', i) + len('**Its changes have not yet been read cold.**')
assert s[j] == '\n', 'App A end'
new = ('- **Later versions.** Each later version made corrections asked for by the reading before it; version 4 also set the mathematics anew, and version 5 the page. '
 'No numbered statement changed in what it states after version 3 (§13). '
 'The changes of each version were read cold by a new reader (cold reader 5 and each later one, from 5 October 2026), with no access to the flights or the audits, '
 'who checked every changed passage against the version before it, re-counted or re-ran with code of its own the numbers and checks it concerned, '
 'and looked at the pdf: at every page, or at the changed pages after comparing all the pages by image. '
 'None of these readings found a gap or an error in the mathematics. '
 'Between them, they found false or inexact sentences in this record and in §12, points of presentation, and defects of typesetting. '
 'This summary replaces a version-by-version account; that account, the list of corrections of each version with its sources, every report and every grading are kept with the project.')
rep(s[i:j], new, 'App A')

for bad in ['version 7', 'this version', 'not yet been read', 'not yet read', 'five days']:
    for m in re.finditer(re.escape(bad), s):
        ln = s.count('\n', 0, m.start()) + 1
        print('CHECK', repr(bad), 'line', ln)
open(P, 'w', encoding='utf-8').write(s)
print('written', P)
