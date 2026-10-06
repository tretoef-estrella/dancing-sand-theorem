# QUERIES — every web search / download, and what it found

## 2026-10-05 13:19:08 CEST — priority and OEIS

1. WebSearch (extended) «Sylow 2-subgroup critical group hypercube complete structure sandpile n-cube» → Bai 2003, Anzis–Prasad 2016 (REU notes), GMMY (Comm. Algebra 2024 / arXiv 1912.06919), Ducey–Jalil 2014, cone/polygon papers. **No result determining the whole 2-part.**
2. WebSearch (extended) «sandpile group folded hypercube critical group folded cube» → same papers plus MathWorld «Folded Cube Graph», quantum automorphisms of folded cubes. **No computation of the sandpile group of the folded cube found.**
3. WebSearch «OEIS A193134» → search engine did not index it; WebFetch https://oeis.org/A193134 → «Numbers of spanning trees of the folded cube graphs», a(2..7) = 1, 16, 4096, 2147483648, 14167099448608935641088, 99884502526333896315983085285953467624610139734016; «defined for n>=2». Matches my eigenvalue formula for n = 3..7 and differs at n = 2 (OEIS counts simple K_2 → 1; Q_2/<1> has a double edge → 2), exactly as the paper says (logs/oeis_check.log).

4. WebFetch https://www-users.cse.umn.edu/~reiner/REU/AnzisPrasad2016.pdf (Anzis–Prasad, «On the critical groups of cubes», UMN REU 2016; GMMY's ref. [1]) → text extracted to scratch/AnzisPrasad2016.txt: upper bound «largest factor in Syl2(K(Qn)) ≤ 2^{n+⌊log2 n⌋}» (Cor. 2.12), a Gröbner-basis conjecture (Conj. 3.11) implying Bai's count, odd Sylows of a cell complex. **Nothing on the whole 2-part, the fold, or tilting.** Not cited by the paper (optional).
5. WebSearch (extended) «tilting modules sandpile group critical group decomposition SL2 characteristic 2» → only SL2 tilting literature (Martin, Tubbenhauer–Wedrich, centres, Clebsch–Gordan in char p). **No sandpile/critical group decomposed over tilting modules.**
6. WebSearch (extended) «Gao Marx-Kuo McDonald Yuen Conjecture 4.14 nth largest cyclic factor hypercube proof» → only GMMY itself; **no other proof found.**
7. WebFetch Semantic Scholar API, citations of arXiv:1912.06919 → 3 citing papers: Reiner–Smith 2024 (arXiv 2402.15453, cones over trees — abstract fetched: nothing on cubes), Yuen 2023, Iga et al. 2022. **No citing paper determines the 2-part.**
8. WebSearch (extended) «"folded hypercube" OR "folded cube" Laplacian Smith normal form invariant factors critical group» → CSX (Smith group of the hypercube), Lorenzini «Smith normal form and Laplacians», «Spectra of Laplacian matrix of folded hypercube» (eigenvalues only). **No critical group of the folded cube.**
9. WebSearch (extended) «arXiv 2025 2026 sandpile group hypercube 2-part Sylow-2 determined all n» → GMMY, Akyar et al. 2026, random-graph distributions. **Nothing newer on the cube.**
10. WebFetch arXiv API, query (sandpile OR "critical group") AND (hypercube OR cube OR folded), newest first, 60 results → 11 entries; only GMMY addresses Syl_2 of Q_n; **none relates the folded cube's group to the cube's.**
11. WebSearch (extended) «"tilting module" "critical group" OR "Smith group" graph Laplacian representation theory Sin» → Sin's school (Grassmann, polar, Paley, Peisert, rook's graphs): modular representation theory of finite classical groups, **not tilting modules of SL2 on cube group rings.**
12. WebSearch (extended) «critical group double cover antipodal quotient hypercube 2-primary halving exponents Reiner Tseng signed graph cube» → Reiner–Tseng (exact sequence; splitting away from 2; cube reinterpretation of Bai's odd part only), 2-fold covers papers. **No fold law.**
Conclusion of the priority search (with the caveat that MathSciNet/zbMATH full text were not searched by me either): I found nothing anticipating the Main Theorem, the fold law, the tilting decomposition, or proofs of GMMY Conj. 4.14 / 5.4.

## bibliographic data of references not in material/sources (2026-10-05)

13. WebSearch «Bier "Remarks on recent formulas of Wilson and Frankl" European Journal of Combinatorics 1993» → cited as Europ. J. Combin. 14 (1993) 1–8 (arXiv 1612.08124 reference list). **Matches [Bie93].**
14. WebSearch «El-Amawy Latifi "Properties and performance of folded hypercubes" …» → IEEE TPDS 2 (1991) 31–42, January 1991 (UNLV repository). **Matches [EL91].** Folded hypercube = hypercube plus complementary edges: confirms the paper's «naming trap».
15. WebSearch «Strassmann "Über den Wertevorrat …"» → J. reine angew. Math. 159 (1928) 13–28, doi 10.1515/crll.1928.159.13. **Matches [Str28].**
16. WebSearch «Kummer "Über die Ergänzungssätze …"» → J. reine angew. Math. 44 (1852) 93–146. **Matches [Kum52].**
17. WebSearch «Kostant "Groups over Z" … Proc. Sympos. Pure Math. 9 1966 pp. 90-98» → PSPUM 9 (1966), ed. Borel, MR0207713; **pages 90–98 not confirmed by the results** (consistent with my memory).
18. WebSearch «Donkin "On tilting modules …" Math. Z. 212 1993 39-60» → widely cited with these data; full record not shown. Consistent.
19. WebSearch «Clausen … Astron. Nachr. 17 1840 351; von Staudt … Crelle 21 1840 372-374» → both confirmed (doi 10.1515/crll.1840.21.372). **Match [Cla40], [vSt40].**
20. WebSearch «Lorenzini … Discrete Math 91 1991 277-282; Biggs … J. Algebraic Combin. 9 1999 25-45» → both confirmed. **Match.**
21. WebSearch «Klivans "The Mathematics of Chip-Firing" CRC Press; Ayer Brunk Ewing Reid Silverman 1955 …» → Klivans CRC Press 2018 confirmed; ABERS not found by the search engine (data consistent with my knowledge: Ann. Math. Statist. 26 (1955) 641–647).
22. WebSearch «Chandler Sin Xiang … Des. Codes Cryptogr. 84 2017 283» → 84 (2017) 283–294 confirmed. WebSearch «Reiner Tseng … Discrete Math 318 2014 10-40; Len Zakharov … Forum Math. Sigma 2022 e11» → LZ22 confirmed (vol. 10, e11); RT14 Discrete Math 2014 confirmed (pages not shown). WebSearch «Ducey Jalil … LAA 445 2014 316-325; Wilson … EJC 11 1990 609-615» → both confirmed.
23. WebSearch «Ducey Hill Sin … LAA 2018; Iga Klivans Kostiuk Yuen … published journal» → DHS17 published in **Linear Algebra Appl. 546 (2018) 154–168**; IKKY published in **Advances in Applied Mathematics**; Yuen 2023 published in **Electron. J. Combin. 31(1) (2024) P1.38**. The paper cites only the arXiv versions of these three.
Not searched (standard textbooks, data certain): Jan03 (AMS Math. Surveys Monogr. 107, 2003), Hum72 (GTM 9, Springer 1972; §26 = «Kostant's theorem»), BBBB72 (Wiley 1972).
