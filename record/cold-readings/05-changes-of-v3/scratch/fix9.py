p='REPORT_COLD_5.md'
s=open(p).read()
old1="The bibliographic data I could check (authors, titles, volumes, years, pages of the nine sources given, and of the classical entries I know) are right."
new1="The bibliographic data I could check are right: the authors and titles of the fourteen papers whose text is in `material/sources/` (first pages read), and, from memory only, the journal data of the classical entries."
old2="- **Cited papers:** I checked the cited items, the two quotations ([Aky26], [GMMY24] Remark 2.13, [CSX17] §5.2) and the bibliographic data of the nine papers given in `material/sources/`; I did **not** read them in full. The bibliographic data of the other 23 references (Kummer, Strassmann, von Staudt, Clausen, Donkin, Humphreys, Jantzen, Klivans, Kostant, Lorenzini, Reiner–Tseng's journal version, Tubbenhauer–Wedrich, Wilson, Bier, Biggs, Ayer et al., Barlow et al., El-Amawy–Latifi, Len–Zakharov's journal version, Ducey–Jalil, Ducey–Hill–Sin, Iga et al.'s and Yuen's journal versions) were checked against my memory only, not against a source."
new2="- **Cited papers:** I checked the cited items, the three quotations ([Aky26], [GMMY24] Remark 2.13, [CSX17] §5.2) and the authors and titles of the fourteen papers whose text is in `material/sources/`; I did **not** read them in full, and the journal data (volume, pages) of their published versions are not in those texts. The data of the other eighteen references ([ABERS55], [BBBB72], [Bie93], [Big99], [Cla40], [Don93], [EL91], [Hum72], [Jan03], [Kli18], [Kos66], [Kum52], [Lor91], [Str28], [TW21], [vSt40], [Wil90]; [OEIS] was checked on the web) were checked against my memory only, not against a source."
assert s.count(old1)==1 and s.count(old2)==1
s=s.replace(old1,new1).replace(old2,new2)
open(p,'w').write(s)
print('ok')
