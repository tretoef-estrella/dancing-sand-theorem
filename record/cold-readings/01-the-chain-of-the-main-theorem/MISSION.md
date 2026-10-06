# COLD READING — «The Dancing Sand Theorem» (the whole 2-part of the sandpile group of the n-cube, for every n)

Written by Grepy Bross, the auditor of the hypercube project, on 4 October 2026 (night). You are a NEW reader, «Grepy el lector frío del cubo 1». You never saw this work being built. Your job is to try to break it.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**SAVE TO DISK AS YOU GO, NEVER AT THE END** (Rafa's permanent order).
1. Before you read anything, create `REPORT_COLD.md` with the section headings of §6, empty.
2. Every verdict goes into `REPORT_COLD.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `CLAUDE.md` (your re-entry note) up to date: one STATE line after each part. If your window is compacted, re-read `MISSION.md` and `REPORT_COLD.md`, and go on.
5. What is not on disk does not exist.

**Where you work**
- Write only inside `~/Desktop/LECTORES_EN_FRIO/CUBO_DANCING_SAND_1/`. Scratch files go there too, never in `/tmp`.
- Never open `~/Desktop/ARBOLYAML/` or `~/Desktop/GREPY_EL_VOLADOR_8/` (another pilot works there on another question, in parallel). Never use `rm`. Never read a Desktop screenshot.
- `material/` is read-only.

**How you run**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate (memory, time) in `logs/DIARY.md` BEFORE each run.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time. Integers and exact fractions only, or exact modular arithmetic.

**Grades of your verdicts, item by item:**
- **HOLDS** — you re-derived it in your own words;
- **GAP** — a step is missing, but you believe the statement;
- **ERROR** — a step is wrong, or the statement is false;
- **PRESENTATION** — the mathematics is fine, the writing is not.

Rules for the verdicts:
- «I did not read it» is an honest verdict. Write it as such.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds. Publish your failures in the same size of type.
- A check whose control cannot fail is not a check.

Chat with Rafa in Spanish; documents in English.

## 1. The claim you are reading

For every n ≥ 1, the 2-part of the sandpile (critical) group of the n-cube Q_n is

**Syl₂ K(Q_n) ⊕ Z₂ ≅ ⊕_λ [ ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ Smith₂ M(λ, (n−λ)/2) ]^{m_λ(n)}**

- The sum runs over the tilting families λ of V^{⊗n} for SL₂ in characteristic 2, with multiplicity m_λ(n).
- k and I come from the binary digits of λ + 1.
- The exponents of Smith₂ M are «the pooled clocks»: the integer antitonic fit (PAVA) of x_D = R_m(D) − R_{m+K}(I∖D).
- Here R_μ(D) = Σ_{t∈D} (h_t − α2^t) − #carries(μ + o_D), with α = 1 for the cube.

All notation is defined in `material/flights/FLIGHT1_REPORT.md` (the rule D.5) and the later reports. The statement as the auditor summarised it is in `material/audits_read_after/AUDIT_FLIGHT_4.md` §4. **Read it only after your own reading.**

**Context.**
- The odd part of K(Q_n) is Bai's (2003). Bai also proved Reiner's 2001 conjectures: the number of 2-factors, and the number of Z/2's.
- The full 2-part was open in every source found:
  - Chandler–Sin–Xiang 2017: «We do not have any conjecture about its exact structure»;
  - Gao–Marx-Kuo–McDonald–Yuen (Comm. Algebra 2024) give its n − 1 largest factors.
- The originals are in `material/sources/` (pdf and text).

## 2. The chain of the proof (the links you must read)

| link | where | what it says |
|---|---|---|
| L1. The tilting families and their multiplicities m_λ(n) (fusion recursion) | FLIGHT1_REPORT | V^{⊗n} over Z₂ splits into tilting lattices T(λ) ⊗ det^i, with multiplicities by a recursion |
| L2. Theorem RT / RT′: the sandpile group splits family by family | FLIGHT1 (RT), FLIGHT3 (RT′, without citing tilting theory) | C ⊗ Z₂ = Z₂ ⊕ Syl₂ K ≅ ⊕_λ X(λ, i)^{m_λ(n)}, with X(λ, i) = coker(F + 2(D + i)) on T(λ) |
| L3. Bier's basis (Theorem Z) and the two moves «doblar» Φ and «dar un paso» V ⊗ Φ; P-R1 | FLIGHT1, FLIGHT2 (A.1, A.2, B.1, C.0) | integral constructions of T(λ); one «doblar» halves the lattice and doubles the payment |
| L4. Theorem D: each X(λ, i) = small clocks ⊕ Smith form of an explicit 2^|I| × 2^|I| matrix M(λ, i) | FLIGHT2 (C.7.4 and around) | the reduction to small matrices |
| L5. The cost form: 2-adic valuations of the entries of M | FLIGHT3, FLIGHT4 (C.4, A.4, §11.2.1–2) | valuations = rulers (carries) + gold γ |
| L6. Theorem O: an upper bound d_r ≤ Y(r) through one minor with a unique cheapest term («the orphan») | FLIGHT3 | the upper bound |
| L7. Theorems U and F: the floor T(r) ≥ Y(r) for every matching, every family, every α ≥ 1, every shift | FLIGHT4 §2 A.5, §11.2 (Mission 4b) | the lower bound |
| L8. The tropical bound d_r ≥ min cost of a matching, and PAVA / integer splitting | standard + FLIGHT4 §11 | closes d_r = Y(r): the rule |
| L9. Base cell → real cells, and the shift i = 0 (the free Z) | FLIGHT4 §11 | every cell, every shift |

**For each link, write in `REPORT_COLD.md`:**
- the statement in your own words;
- your verdict (HOLDS / GAP / ERROR / PRESENTATION);
- the exact line or step where a doubt lives;
- which external facts it uses, and whether they are used correctly: PAVA (Ayer–Brunk–Ewing–Reid–Silverman 1955), Bier 1993, Kummer's carries, and standard facts on tilting modules if any remain.

## 3. Checks with your own code (independent of the flights' engines)
1. **Direct computation.** Compute Syl₂ K(Q_n) directly from the Laplacian of Q_n, with your own exact Smith form, for n = 2..10 (n = 11 if your estimate fits the caps; the auditor's numpy-mod-2^30 route did n = 12 in 196 s and 980 MB, close to the cap). Compare with the rule as printed.
   - **Control:** the rule with one ingredient removed — no pooling, or the carries read at m instead of m + K — must fail somewhere.
2. **Bai's table and counts.** Compare the rule with Bai's printed table (`material/sources/Bai_cube_group_LAA2003.*`). Watch out: pdftotext drops superscript 1's. Then compare with his counts 2^{n−1} − 1 and the number of Z/2's, for n ≤ 60, by the rule.
3. **Gao et al.** Compare the rule with their n − 1 largest factors (Theorem in `material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.*`), n ≤ 30.
4. **One link by machine.** Pick the link you trust least among L5–L7 and gate it on small families (λ ≤ 30) with your own code.

The flights' engines are in `material/engines_of_the_flights/`. Use them only to reproduce a number you doubt; copy them into `engines/` first. Your verdicts must not rest on them.

## 4. Priority and credit
- Is this the first statement of the whole 2-part of K(Q_n)? Read the sources given; say what they say, with page and line.
- Are Bai's and Gao's results credited correctly?
- **Nearest precedents** named by the auditor:
  - Ducey et al. 2023, `SubsetIntersection_arXiv2310.09227` (the Johnson scheme);
  - Chandler–Sin–Xiang (the adjacency matrix of the cube);
  - Doty–Henke (tilting decomposition of V^{⊗n} in characteristic 2).

  Is our fusion recursion theirs? Is anything of ours in them?
- You may do web searches. Write each query and what it found.

## 5. Order and budget
- Part 1 (15 %): the statement, L1, L2, and check 1 (direct computation).
- Part 2 (45 %): L3 to L7, link by link. L6 and L7 are the heart.
- Part 3 (20 %): L8, L9, and checks 2–4.
- Part 4 (10 %): priority and credit (§4).
- Part 5 (10 %): writing.
- After everything else: read `material/audits_read_after/` and say where you disagree with the auditor.

Ten minutes without traction on a link: write what you have, mark it, go on.

## 6. Sections of REPORT_COLD.md (create them empty first)
0. First line — does the Dancing Sand Theorem hold as stated: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD
1. The statement as I read it
2. The chain, link by link (L1–L9: statement, verdict, doubts, external facts)
3. Checks with my own code (with controls)
4. Priority and credit
5. Where I disagree with the auditor's audits
6. Sealed predictions, hits and failures
7. My errors
8. What I did not read
9. Files with md5
