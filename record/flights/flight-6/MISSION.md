# MISSION 6 — «Grepy el volador 6»: GAO'S CONJECTURE 5.4 AND THE FOLD LAW, FOR EVERY n

Written by Grepy Hypercube, the auditor of the hypercube project, on 4 October 2026. You are a NEW constructor (Rafa's order: a fresh Claude for each mission). You never met the five pilots before you. Everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.** Flight 5 broke this twice (its errors E4, E5): it did a long stretch of pencil before writing it, and it wrote its estimates after the pencil. **DO NOT REPEAT IT.**
1. Before you think anything, create `REPORT.md` with the section headings of §7, empty.
2. **Every lemma goes into `REPORT.md` the moment you have it**, before you look for the next one. Twenty minutes of pencil not on disk is a broken rule.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Write the leg's estimate in `REPORT.md` BEFORE you start the leg, and each run's estimate BEFORE the run.
5. Keep `CLAUDE.md` (your re-entry note) up to date. If your window is compacted, re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, then go on from the last leg that is not CLOSED.
6. What is not on disk does not exist. Tell in `REPORT.md` §8, in plain words, how each idea came: Rafa wants the story.

**Where you work**
- Write only inside `~/Desktop/GREPY_EL_VOLADOR_6/`. Scratch files go there too, never in `/tmp`.
- Never open `~/Desktop/ARBOLYAML/`. Never use `rm`.

**How you run**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- Never expand a huge multiplicity into a list: count with integers.
- One heavy job at a time.

**Grades:** **PROVED** (pencil, with a gate), **MEASURED**, **READING**, **CONJECTURE**.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it.
- Publish failures in the same size of type.
- A control must be able to fail.

Chat with Rafa in Spanish; documents in English.

## 1. Where the cube stands

The sandpile group `K(Q_n)` of the n-cube has its 2-part known for every n, by a closed rule. This was proved by flights 1–4, audited (`material/AUDIT_FLIGHT_4.md`):

  **Syl₂ K(Q_n) ⊕ Z₂ ≅ ⊕_λ [ ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ Smith₂ M(λ, (n−λ)/2) ]^{m_λ(n)}**

Here λ + 1 = 2^k + Σ_{t∈I} 2^t. The big clocks are the integer PAVA, «ceil first», of the raw clocks.

**Read flight 5 first** (`material/FLIGHT5_REPORT.md`, audited in `material/AUDIT_FLIGHT_5.md`). It writes the raw clock in absolute terms: **u(D) = φ(x) + κ(J−1, x) + h(D)**, where
- J = i + o_D and x = n − 2J + 1;
- φ(x) = x + v₂x;
- κ = number of carries;
- h(D) = the gold.

It proves the ceiling of every family at shift i ≥ 1 (its Theorem C), and from it the podium: Gao et al.'s Conjecture 4.14 and the poster's (n+1)-th factor, for every n. Its library `material/flight5_engines/f5lib.py`, and the auditor's `material/auditor_flight5/gh_audit_vuelo5.py`, evaluate the rule in seconds. Evaluating the PROVED rule is arithmetic, not measuring.

## 2. Your targets

**TROPHY 3 — Gao et al.'s Conjecture 5.4** (`material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt`, line 1179), for every k ≥ 1:

  **Syl₂ K(Q_{2^k}) ≅ Syl₂ K(Q_{2^k−1})² × Z/2^{2^k+k−1}**

In words: every factor of the cube 2^k − 1 appears twice, plus one top factor (Gao's c₁, their Theorem 4.1).
- The auditor's measurement from the rule, k = 1..9 (n ≤ 512): **it holds**. A control (without the top factor) fails. Log: `material/auditor_flight5/gh_audit_conj54.log`.
- Gao et al. say a proof «can help building a bridge» to the Smith group.

**THE FOLD LAW** (`material/fold_law/THE_FOLD_LAW_PENCIL_NOTE_v2.md`, read it whole). Write `K̄(n)` for the sandpile group of the folded cube (`Q_n` with each corner glued to its opposite, `a = x₁⋯x_n`). For every n:

  **2·K(Q_n) ≅ K̄(n) on 2-parts**,

that is,

  **Syl₂ K(Q_n) ≅ (Z/2)^{a_n} ⊕ [Syl₂ K̄(n) with every exponent raised by one]**, where a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}.

- MEASURED for n = 3..13 (whole groups). The engine `material/fold_law/turnos.py` computes `K̄` directly; its log `turnos_3_12.log` is there.
- PROVED (note §1.4 and §6): its layers 0 and 1, by the switches and the first carry.
- OPEN: layers j ≥ 2.
- Useful facts already proved in the note:
  - `K̄ ≅ (1 + a)K` (§1.2, and Reiner–Tseng's exact sequence; the source is in `material/sources/`);
  - `2C ≅ R'/(θ)` and `C̄ = R'/(f)`, with θ and f having the same valuation on every character (§1.3);
  - `N_U K ≅ K(Q_n/U)` for every subgroup U (§7.1).

## 3. The idea that should make it arithmetic (READING, for you to test, not to trust)

The fold law is a statement about two groups. Only one of them, `K(Q_n)`, has a closed rule. **The fold law becomes arithmetic the moment `K̄(n)` has a closed rule of its own.**
- Since `K̄ ≅ (1 + a)K`, look for how `a` acts on the pieces of Theorem D.
- Over Q, `a` acts on a character with j minus signs by (−1)^j; that character space is the weight μ = n − 2j part of flight 1's picture. So, rationally, `a` is the sign (−1)^{(n−μ)/2}.
- On the dancer D of a family at shift i, the weight is μ = n − 2J with J = i + o_D. So, rationally, `a` is (−1)^J on that dancer. Over Z_2 it is not diagonal (`x_i s_S = s_S − s_{S∪i}` for i ∉ S); what you need is its action on each family's Smith form.
- Find what `(1 + a)` does to each family's Smith form. The candidate to test first is the fold law FAMILY BY FAMILY: `K̄` is the same sum over families, with each family's clocks lowered by one, and the Z/2's (the a_n) coming out family by family. This candidate is stronger than the fold law, so proving it would prove the law. If it is false family by family, say where it fails and look for the right pairing of pieces.
- Check every candidate first against `turnos.py` for n ≤ 12.

## 4. The legs (in this order; each ends CLOSED, AGOTADO or NO CONCLUYO)

**Leg 0 — calibration (budget 15 %).** Prove from the rule, by pencil, Bai's two counts (2003):
- the number of cyclic factors of Syl₂ K(Q_n) is 2^{n−1} − 1;
- the number of factors Z/2 is a_n = 2^{n−2} − 2^{⌊(n−2)/2⌋}.

(The auditor checked both from the rule for n ≤ 15: `material/auditor_flight5/gh_bai_counts.log`.) If the rule cannot give them, stop and report why. They are the fold law's layer 0 and its a_n, so this is your test.

**Leg A — Trophy 3, Conjecture 5.4, for every k (budget 30 %).**
- Families of n = 2^k − 1 are odd and families of n = 2^k are even. Find how the families, their multiplicities and their clocks of the two cubes correspond: a family of the smaller cube should give two copies in the larger.
- The top factor 2^k + k − 1 is flight 5's V₀ = φ(n) − 1 at n = 2^k.
- Prove it for every k. Gate against the rule for k ≤ 9.

**Leg B — the folded cube's rule (budget 35 %; the heart).**
- Find and prove a closed rule for Syl₂ K̄(n), following §3 or any better route.
- Gate it against `turnos.py` for n ≤ 12 (whole group, estimate first), and the proved layers 0 and 1 of the note for larger n.

**Leg C — the fold law for every n (budget 20 %).**
- From the two rules, prove `2K ≅ K̄` on 2-parts for every n. Name every dependency.
- Gate against the measured n = 3..13.
- **Kill criterion:** if the fold law fails for some n, that is the first line of the report, with the smallest n.

**Not in this mission:** the extension of the fold law to other folds (note §7.3), the novelty sweep (the auditor does it), the paper.

## 5. The house vocabulary (Rafa's images; say which served)

- **The rent:** no matching is cheaper than the natural one at any rent.
- **The gold:** the gaps a dancing couple skips.
- **The plumber and the flat that owes its mirror:** one price per shared flat.
- **«Binario, o está o no está, en secado o en mojado, y en el doble de horas»:** halving and doubling of the clocks.
- **«Se van turnando»:** each corner is the dry one for exactly one sink, its opposite. This image found the fold law.
- **The wound:** the sink heals by rotating; folding again is doubling.

For this flight, think of **the mirror that doubles**:
- folding the cube by its opposite corner is the same as doubling it, except for a layer of Z/2's;
- the cube 2^k is the cube 2^k − 1 seen twice in a mirror, plus one tower on top.

## 6. Budget

- Write the estimate before each leg.
- If ten minutes pass without traction, stop, write what you have, and mark the leg AGOTADO.
- Keep the last fifth of your time for writing.

## 7. Sections of REPORT.md (create them empty first)

0. First line — what this flight closes and what it does not
1. Leg 0 — calibration (Bai's counts from the rule)
2. Leg A — Conjecture 5.4
3. Leg B — the folded cube's rule
4. Leg C — the fold law for every n
5. Images — which served
6. Sealed predictions, hits and failures
7. My errors
8. The story of this flight, in plain words
9. Files with md5

Note: the auditor's and older engines in `material/` use their authors' paths.
- Copy any that you run into `engines/` and fix its paths. For example, `gh_audit_vuelo5.py` execs `engines_gh/gh_audit_vuelo2.py`; the file is in `material/auditor_flight5/`.
- `material/fold_law/turnos.py` imports `capas.py` from its own folder.
