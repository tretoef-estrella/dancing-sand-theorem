# COLD READING — «The fold law (the Dry and Wet law) for every n»

Written by Grepy Bross, the auditor of the hypercube project, on 5 October 2026 (morning). You are a NEW reader, «Grepy el lector frío del cubo 2». You never saw this work being built. Your job is to try to break it.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**SAVE TO DISK AS YOU GO, NEVER AT THE END** (Rafa's permanent order):
1. Before you read anything, create `REPORT_COLD.md` with the section headings of §6, empty.
2. Every verdict goes into `REPORT_COLD.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `CLAUDE.md` (your re-entry note) up to date: one STATE line after each part. If your window is compacted, re-read `MISSION.md`, `CLAUDE.md` and `REPORT_COLD.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside `~/Desktop/LECTORES_EN_FRIO/CUBO_FOLD_LAW_1/`. Scratch files go there too, never in `/tmp`.
- Never open `~/Desktop/ARBOLYAML/` or any `~/Desktop/GREPY_EL_VOLADOR*` folder. Never use `rm`. Never read a Desktop screenshot.
- `material/` is read-only.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate (memory, time) in `logs/DIARY.md` BEFORE each run.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time. Use integers and exact fractions only, or exact modular arithmetic.

**How you grade, item by item:**
- **HOLDS** — you re-derived it in your own words;
- **GAP** — a step is missing, but you believe the statement;
- **ERROR** — a step is wrong, or the statement is false;
- **PRESENTATION** — the mathematics is fine, the writing is not.

**Honesty rules.**
- «I did not read it» is an honest verdict: write it as such.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds, and publish your failures in the same size of type.
- A check whose control cannot fail is not a check.
- Chat with Rafa in Spanish; write documents in English.

## 1. The claim you are reading

For every n ≥ 1, with K(Q_n) the sandpile (critical) group of the n-cube and K̄(n) that of the folded n-cube (Q_n with antipodal vertices identified):

**Syl₂ K(Q_n) ≅ (Z/2)^(a_n) ⊕ [Syl₂ K̄(n) with every exponent raised by one],  a_n = 2^(n−2) − 2^⌊(n−2)/2⌋;**

equivalently, Syl₂ K̄(n) ≅ 2·Syl₂ K(Q_n).

- The claim is PROVED by pencil on two readings: the pilot's (flight 9) and the auditor's.
- **Status of its parts:**
  - the mod-2 layer was read cold once (`material/audits_read_after/COLD_AUDIT_FOLD_LAW_v2.md` — read it only after your own reading);
  - the whole law for n ≤ 144 rests on machine certificates (flight 8, Theorem C₈);
  - **the law for every n rests on flight 9's Lemma Ω, which nobody outside the project has read.** That is your main target.
- The sandpile group of the cube itself (the «Dancing Sand Theorem», flights 1–5) has had its own cold reading. **You may use flights 1–5 as background, but every step of flights 6–9 is yours to check.**

## 2. The chain of the proof (the links you must read)

| link | where | what it says |
|---|---|---|
| F1. Family by family | FLIGHT6 §3.1 (Lemma RT̄), §1.3 (Lemma S); FLIGHT1/FLIGHT3 (RT, RT′) | both groups split over the tilting families λ of V^⊗n with the same multiplicities; T(0) never occurs |
| F2. The fold law from the family law | FLIGHT6 §4.2, FLIGHT7 §3.1, FLIGHT8 §3.1 | it suffices that X̄(λ, i) ≅ 2X(λ, i) for every family λ and shift i |
| F3. The operators | FLIGHT7: Lemma A0 (2X ≅ T/(τ, e₂)T), Lemma H-odd, Lemma H-even; FLIGHT2 A.2 (P-R1) | odd family: X̄(2l+1, j) = coker(Ψ_j on T(l)), Ψ_j = 2(2D + j) + (Ch − (−1)^j)Sh⁻¹ |
| F4. Even families as two glued arms | FLIGHT8 §1.3 (E2), §2.4 (E3), §2.8 (E4) | even family = glue(Ψ_{i+1}, Ψ_i); its doubled system = folded × the bend |
| F5. The formal dance | FLIGHT2 C.0, FLIGHT8 §2.6, `material/engines_of_the_flights/fdance.py` | the cokernel on T(l) is computed by a chain of moves «doblar» / «paso» (Schur complements divided by 2) |
| F6. Lemma IB and its Corollary | FLIGHT9 §2.1 | the inverse of each level is a block of A⁻¹; each final-matrix entry is (constant) × one coefficient of A⁻¹ |
| F7. Lemma PS | FLIGHT9 §2.1 | the path sum: y^A = y^Σ(1 + ε), v(ε) ≥ α − 1 |
| F8. Lemma H | FLIGHT9 §2.1, with FLIGHT2 C.4 and the superadditivity of δ (FLIGHT3) | Hadamard twists of M_Σ⁻¹ invert to Hadamard twists of M_Σ |
| F9. Theorem R | FLIGHT9 §2.1, with Theorems O (FLIGHT3) and F (FLIGHT4) | rigidity of the final matrix, if the dance is clean |
| F10. The class 𝒦, Theorem C | FLIGHT9 §2.2 (K1, K2, T1, T2; the doblar; the paso = V-split + doblar) | every move of the dance is clean; **the heart of the proof** |
| F11. Ω-odd and shift 0 | FLIGHT9 §2.3 | including the continuity argument at c = 0 and the reduction of the real weights (tanh, coth) to normal form |
| F12. Claim A and Lemma U | FLIGHT9 §4.1–4.2 | the dance mod 2 sees only the operator mod 2; the glue passes to the bottom of the dance |
| F13. Lemma B | FLIGHT9 §4.3 | the window bound: the bend is a unit ≡ I mod 2 at the bottom |
| F14. Ω-even and shift 0 | FLIGHT9 §4.4 | the two even final matrices are associates |
| F15. Assembly | FLIGHT9 §5.1 | every dependency named |

**For each link, write in `REPORT_COLD.md`:**
- the statement in your own words;
- your verdict;
- the exact line or step where any doubt lives;
- the external facts it uses (Strassmann's theorem, Legendre, the block-inverse identity, Schur complements), and whether they are used correctly.

**Read these hardest:**
- Theorem C (does Θ really kill every shift, is Θ(Dd) = 0, is β² = 0, and does the paso equal V-split + doblar with fdance's conventions?);
- Lemma H (the chain bound);
- Lemma B (the window bound);
- the two continuity arguments at shift 0.

## 3. Checks with your own code (independent of the flights' engines)
1. **Direct computation of the law.** Compute Syl₂ K(Q_n) and Syl₂ K̄(n) from their Laplacians with your own exact Smith form, n = 2..11 (n = 12 only if your estimate fits the caps), and compare with the law.
   - **Control:** the law with a_n changed by ±1, or with the shift by one removed, must fail.
2. **Theorem C beyond the pilot's gates.**
   - The pilot gated Theorem C only with constant weights. The auditor added floor-dependent 𝒦 weights.
   - Design your own test of the induction step: build a level system in the class (genuinely floor-dependent 𝒦 functions, several dancers), apply ONE doblar and ONE paso by your own implementation of the slot formulas printed in FLIGHT9 §2.2, and check cleanliness and conditions (a), (b).
   - **Control:** a system NOT in the class (for example, payments 2y, or random odd units on F together with weights ζ_m) must break somewhere. Beware: random odd units on F with no weights cannot fail, because a floor unit conjugates them to 1.
3. **One link by machine.** Pick the link you trust least among F7, F8 and F13, and gate it with your own code.
4. **The engines of the flights** are in `material/engines_of_the_flights/`. Use them only to reproduce a number you doubt; copy them into `engines/` first. Your verdicts must not rest on them.

## 4. Priority and credit
- **Is the fold law (or «2K(Q_n) ≅ K(folded cube)») stated anywhere before?** Read `material/sources/` (Reiner–Tseng arXiv:1301.2977 has an exact sequence relating the cube and the folded cube; Gao–Marx-Kuo–McDonald–Yuen arXiv:1912.06919, Remark 2.13, asks for a «deeper connection»; Bai 2003; Chandler–Sin–Xiang). Say what they say, with page and line.
- Is the class 𝒦 (functions a + 2χ(2y)) or Theorem C's mechanism a known tool?
- You may do web searches and download arXiv papers for reading. Write each query and what it found.

## 5. Order and budget
- Part 1 (15 %): the claim, F1–F3, and check 1.
- Part 2 (50 %): F5–F14, link by link. F10 is the heart.
- Part 3 (15 %): F15 and checks 2–3.
- Part 4 (10 %): priority (§4).
- Part 5 (10 %): writing.
- After everything else, read `material/audits_read_after/` and say where you disagree with the auditor.
- Ten minutes without traction on a link: write what you have, mark it, go on.

## 6. Sections of REPORT_COLD.md (create them empty first)
0. First line — does the fold law for every n hold as stated: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD
1. The claim as I read it
2. The chain, link by link (F1–F15)
3. Checks with my own code (with controls)
4. Priority and credit
5. Where I disagree with the auditor
6. Sealed predictions, hits and failures
7. My errors
8. What I did not read
9. Files with md5
