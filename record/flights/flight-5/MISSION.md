# MISSION 5 — «Grepy el volador 5»: THE TWO TROPHIES (Gao et al.'s Conjecture 4.14 and the poster's (n+1)-th factor, for every n)

Written by Grepy Hypercube, the auditor of the hypercube project, on 3 October 2026. You are a NEW constructor: Rafa's order is a fresh Claude for each mission, for hygiene. You never met the four pilots before you. Everything you need is in this folder.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**RAFA'S PERMANENT ORDER: SAVE TO DISK AS YOU GO, NEVER AT THE END.**
1. Before you think anything, create `REPORT.md` with the section headings of §7, empty.
2. Put every result into `REPORT.md` before you take the next step.
3. Before and after each step, write one line in `logs/DIARY.md` with the time. Paste the time from `date`; never type it from memory.
4. Keep `CLAUDE.md` (your re-entry note) up to date. If your window is compacted, re-read `MISSION.md`, `REPORT.md` and `checks/SEALED.md`, and go on from the last leg that is not CLOSED.
5. What is not on disk does not exist. Write in `REPORT.md` §8, in plain words, how each idea came: Rafa wants the story.

**Where you work**
- Write only inside `~/Desktop/GREPY_EL_VOLADOR_5/`. Scratch files go there too, never in a scratchpad or `/tmp`.
- Never open `~/Desktop/ARBOLYAML/`. Never use `rm`.

**How you run**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder; the log is the FIRST argument.
- Write an estimate of memory and time before each run.
- The caps are 1.2 GB and 10 minutes, and they are not raised.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time: other sessions use this Mac.

**Grades and predictions**
- Grade everything: **PROVED** (pencil, with a gate), **MEASURED**, **READING** or **CONJECTURE**.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it. Publish the failures in the same size of type.
- A control must be able to fail.

Chat with Rafa in Spanish; write documents in English.

## 1. Where the cube stands — it is CLOSED

`K(Q_n)` is the sandpile group of the n-cube. Its 2-part was open from Bai (2003) until today. Read whole `material/FLIGHT4_REPORT.md` §11 and `material/AUDIT_FLIGHT_4.md`. Read flights 1–3 as you need them.

**THE THEOREM (flights 1–4, audited).** For every n ≥ 1:

  **Syl₂ K(Q_n) ⊕ Z₂ ≅ ⊕_λ [ ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ Smith₂ M(λ, (n−λ)/2) ]^{m_λ(n)}**

The pieces:
- **Families.** The sum runs over the families λ ≡ n (mod 2), with λ + 1 = 2^k + Σ_{t∈I} 2^t. The multiplicities m_λ(n) come from the fusion recursion (flight 1).
- **Big clocks.** The exponents of Smith₂ M(λ, i) are the **pooled clocks**: the integer PAVA, «ceil first», of
  x_D = R_m(D) − R_{m+K}(I∖D), with m = i − 1, K = 2^k,
  R_μ(D) = Σ_{t∈D}(h_t − 2^t) − #carries(μ + o_D),
  plus a normalising constant.
- **Small clocks.** They are the first bracket.
- **In practice.** `material/flight2_engines/rulew.py` (`H_rule`, `naive_u`, `pool`) and `material/flight1_engines/rule.py` evaluate the rule.
- **What it means.** The rule is now a THEOREM, so every statement about Syl₂ K(Q_n) is ARITHMETIC on the rule. No Smith form and no matching is left.

## 2. Your target: two open statements, for every n

Write c_j(Q_n) for the j-th largest cyclic factor of Syl₂ K(Q_n), counted with multiplicity (exponents v₂). The sources are `material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt`, around line 890 and line 1156, and `material/sources/GaoMarxKuoMcDonald_JMMposter2019.txt`, line 11.
- **Gao et al., Theorem 4.1 (proved by them):** v₂(c₁(Q_n)) = max( max_{x<n}(v₂x + x), v₂n + n − 1 ).
- **Gao et al., Theorem 4.2 (proved by them):** v₂(c₂) = … = v₂(c_{n−1}) = max_{x<n}(v₂x + x).
- **TROPHY T1 — Gao et al., Conjecture 4.14 (open):** for n ≥ 3, **v₂(c_n(Q_n)) = max( max_{x<n−1}(v₂x + x), v₂(n−1) + n − 3 ).**
- **TROPHY T2 — the JMM 2019 poster (open):** for n ≥ 4, **v₂(c_{n+1}(Q_n)) = max_{x<n−1}(v₂x + x).**

Flight 3 evaluated both on the proved groups for n ≤ 261 and odd n ≤ 299 (P-C2/C4/C5): they hold there. **Your job is a pencil proof for every n.**

## 3. The auditor's measurement — where the trophies live (MEASURED; `material/auditor_flight4/gh_trofeos_quien.log`)

For every n ≤ 40, and for n = 48, 63, 64, the factors in positions n − 1, n and n + 1 come from the families **λ ∈ {n, n − 2, n − 4}**, that is, the shifts **i = (n − λ)/2 ∈ {0, 1, 2}**. In the log each tuple is (position, exponent, λ, |I|).
- |I| is not bounded: it is 5 at n = 64.
- Examples:
  - n = 33: position 33 comes from λ = 33 (i = 0) and position 34 from λ = 29 (i = 2).
  - n = 64: positions 63–65 come from λ = 62 (i = 1, |I| = 5).

At these shifts the clocks are explicit:
- **i = 1** (m = 0) is an all-short cell. The pooled clocks are Theorem RW's reflected walk with τ_t = h_t − 2^t (flight 4 A.3).
- **i = 0** is the house m_low = 2^k − 1 with row ∅ deleted (flight 4 A.6 and 11.2.6 (b)): R(D) = τ(D) + min D.
- **i = 2** (m = 1) has one carry at bit 0. Use the gate algebra of flight 4 §11.2.1.

## 4. The legs (in this order; each ends CLOSED, AGOTADO or NO CONCLUYO)

**Leg 0 — calibration: re-derive Gao's Theorems 4.1 and 4.2 from the rule (budget 25 %).** These are known, so they are the test of your method. Write the rule's exponents in absolute terms: fix the normalising constant against `rulew.py` and against Gao's c₁. Then find which family and which clock gives c₁ and c₂…c_{n−1}, and prove both theorems by pencil from the rule. If your method cannot reproduce 4.1 and 4.2, stop and report why.

**Leg A — the explicit clocks at i = 0, 1, 2 (budget 25 %).** For every family λ with shift i ∈ {0, 1, 2}:
- write its big clocks in closed form (reflected walk; with carries at i = 2);
- write its small clocks;
- write the multiplicities m_n(n), m_{n−2}(n), m_{n−4}(n) from the fusion recursion, in closed form.

Seal your formulas, then gate them against `rulew.py` for n ≤ 300. Evaluating the PROVED rule is arithmetic, not measuring houses, so it is allowed.

**Leg B — the uniform bound (budget 30 %; the heart).** Prove that every other cyclic factor has exponent ≤ the target value, and count multiplicities exactly. «Every other» means:
- every family with shift i ≥ 3;
- every small clock;
- the remaining clocks of the families at i ≤ 2.

The goal is to locate positions n and n + 1 exactly. Tools already proved:
- Lemma Λ: |ŷ| ≤ α(2^k − 1) for the pooled clocks (flight 4, 11.2.6 step 2);
- the explicit cost form (flight 4 A.4);
- small clocks are ≤ k − 1.

Find how the exponent depends on i, so that larger shifts give smaller clocks. Seal the lemma before gating it.

**Leg C — assembly.** Prove T1 and T2 for every n (n ≥ 3 and n ≥ 4 respectively), with every dependency named. Gate the final statements against the rule for every n ≤ 300 and against flight 3's table. **Kill criterion:** if T1 or T2 fails for some n, that is the first line of the report, with the smallest n.

**Not in this mission** (later missions, Rafa's order): Conjecture 5.4, the fold law, and the novelty sweep of Theorem D. Do not start them.

## 5. The house vocabulary (Rafa's images, constant across flights; use them if they help, and say which served)

- **The rent:** the floor is «no matching is cheaper than the natural one at any rent».
- **The gold:** the gaps a dancing couple skips.
- **The plumber and the flat that owes its mirror:** one price per shared flat, set between its two halves.
- **«Binario, o está o no está, en secado o en mojado, y en el doble de horas»:** halving and doubling of the clocks.

For this flight, think of **the podium**:
- the top n − 1 places are already known (Gao);
- you must say who stands on steps n and n + 1, and prove that nobody from the crowd (larger shifts, small clocks) can climb above them.

## 6. Budget

Write the estimate in `REPORT.md` before starting each leg. If ten minutes pass with no traction, stop, write what you have and mark the leg AGOTADO. Keep the last fifth of your time for writing.

## 7. Sections of REPORT.md (create them empty first)

0. First line — what this flight closes and what it does not
1. Leg 0 — calibration (Gao 4.1, 4.2 from the rule)
2. Leg A — explicit clocks and multiplicities at i = 0, 1, 2
3. Leg B — the uniform bound
4. Leg C — assembly: T1 and T2 for every n
5. Images — which served
6. Sealed predictions, hits and failures
7. My errors
8. The story of this flight, in plain words
9. Files with md5

Note: the auditor's engines in `material/auditor_flight4/` use the auditor's paths. If you run them, copy them to `engines/` and fix their paths, for example `rulew.py` is in `material/flight2_engines/`.
