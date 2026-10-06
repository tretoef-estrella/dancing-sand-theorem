# The story and the numbers

How the 2-part of the sandpile group of the cube was found and checked, told as it happened, with the dead ends and the failed predictions. The mathematics stands on its own, in [the paper](paper/THE_DANCING_SAND_THEOREM_v8.pdf); this page is the record of how it was made.

## Who did what

The proofs were not found by one mind. They were found by separate instances of **Claude**, Anthropic's AI, each working in its own role and its own folder, under the direction of **Rafael Amichis Luengo**:

- **Constructors** («Grepy el volador» 1 to 9, the nine «flights») each received a written mission. Each found and wrote proofs, sealed its predictions on disk before measuring, and handed in a report.
- **Auditors** (Grepy Chats, Grepy Hypercube, Grepy Bross, Grepy Muchas Pilas, Grepy Escribano, one after another) re-derived every step of every flight in their own words. They marked each step CORRECT, GAP or ERROR and ran their own engines, never the constructor's. They also wrote the missions and the paper. Grepy Mandalay, the auditor of the author's previous project, brought tools from it.
- **Cold readers** (ten of them) read the chains of proof, and then the text, without ever seeing the audits, and wrote their own code.
- **The author** chose the problem among those proposed, decided what to attack and when to stop, and kept the team honest. Again and again, when the team was stuck, he gave an everyday image that was translated into mathematics.

Every computation ran inside a watchdog that limits memory and time. A result counted only if its log ended with the watchdog's final line.

## How it went

**Choosing the problem.**
- The author asked for an open problem «within reach, not impossible, not only for specialists».
- The auditor proposed the 2-part of the sandpile group of the cube. It was open since Bai (2003), and it is the degree-2 member of the family of group rings the author had worked on for three months.
- His estimate of the odds of proving the whole theorem was one in four.
- Early on, the fold law was found, as a measurement (below), and its first two layers were proved by pencil.

**The rule.** Four flights closed the Main Theorem:
- **Flight 1** split the cube over tilting modules and wrote down a closed rule as a conjecture. The auditor checked it 15 of 15 with his own engines.
- **Flight 2** found the integral doubling functor `Φ` and the dance (Theorem D). The group was now the Smith form of small explicit matrices, but one step was open: the pooling.
- **Flight 3** proved the ceiling (Theorem O, the unique cheapest matching).
- **Flight 4** proved the floor (Theorem F).

Then the auditor read the proof of Theorem F by hand, step by step, and ran his own engine on every family `λ ≤ 254` with no failure. The rule held for every `n`, on two readings.

**The trophies and the fold.**
- **Flight 5** proved Gao et al.'s Conjecture 4.14 and the `(n+1)`-th factor of the 2019 poster.
- **Flight 6** proved Conjecture 5.4, and the fold law up to `n = 21`.
- **Flights 7 and 8** carried the fold law to every `n ≤ 100`, then to every `n ≤ 144`, and proved its mod-2 layer for every `n`. They did not close it.
- **The first cold reader** read the chain of the Main Theorem and wrote: «holds».

**The fold closes, and the paper.**
- **Flight 9** proved the last lemma of the fold law (Lemma Ω), so the fold law holds for every `n`.
- **The second cold reader** read the chain of the fold law and wrote: «holds».
- A literature search followed: every source read in the original, the citation trees followed.
- Then the paper was written.
- **The third cold reader** read it whole and wrote «holds with gaps». It found one gap: the integer part of Lemma 7.2(b) was false as stated. No theorem was affected; its own repair, re-derived, went into version 2.
- **The fourth reader** confirmed the repair, and proved that the rounding in the rule never acts.

**Eight versions.**
- Version 3 strengthened Lemma 7.9 and added two missing hypotheses (Lemmas 10.6(a) and 10.10). Versions 4 to 8 changed no numbered statement.
- What they changed was sentences of the record of the work, the verification tables, and above all the typesetting of the PDF. Each version's changes were read cold by a new reader.
- Version 8 was published on Zenodo.

## The images

The author does not write mathematics. What he gave were pictures, in Spanish, often in a single message. The auditor's rule was to **translate each picture piece by piece into something that can be counted, seal the translation on disk, and only then measure**. Most pictures died on contact with the numbers. Some opened the way. Here are a few, with what they became; the original words are in Spanish, translated here.

- **«They must take turns; otherwise they would always stay wet.»** The first measurement showed that the corner opposite the sink is almost dry, and the auditor reported it as a curiosity. The author answered that the corners must take turns, and that this might be the rule. It was: each corner is the dry one for exactly one sink, its opposite. So the auditor folded the cube, gluing each corner to its opposite, and measured the **fold law** — the folded cube's group is the cube's with every exponent lowered by one — in dimensions 3 to 13. Dimension 13 was predicted with no free parameter, sealed, and hit.
- **«Dry or wet, double the hours, like the powers of two.»** Modulo 2 the cube splits into on/off switches: the cube's operator is their sum, the folded cube's their product. This became the pencil proof of the first layer of the fold law. It also gave the fold law its name: «dry» is modulo 2, «wet» is over the 2-adic integers.
- **«Climbing in the air: colder, lower pressure, not only the altitude.»** Written out, one step up an edge of the cube is `U + 2D`: «one step up» plus twice «the height». The carries beyond modulo 2 are the binary digits of the height, one by one. This proved the second layer of the fold law.
- **The orphan.** «One parent is gone and the one who is left takes care of everything; nobody has to be killed, it died by itself.» In every natural minor of the final matrix exactly one matching is the cheapest. This is **Theorem O**, the ceiling.
- **The flat that owes money to its mirror.** «What you don't pay the landlord you give to me; that is why it has to be negotiated together.» A tenant and its mirror keep one account. Each new binary digit creates one new flat, mirror of itself, whose price always fits between its two halves. This is **Theorem F**, the floor, which closed the rule for every family.
- **«Force it to weigh differently.»** At `α = 2` the weights could not be forced to move the hands of the clocks, not even weights of `2^40` (616 tries of 616). The only place where they moved was `α = 1` with the first weight odd. That was the signature of a structural law, the rigidity of §10.
- **The cave.** «The deeper you go, do everything by half; the hole narrows; it is the only way down, as in *The Shawshank Redemption*.» It told flight 9 what to measure. The coefficients of every level are functions of twice the position: the ring `𝒦` of Theorem 10.15, the heart of the fold law. The pilot wrote afterwards: «Without the measurement "h + 2" I would not have looked for functions of 2y.»
- **«The hinges come in pairs; the bugs are findings.»** The auditor's weights had been random. That was the bug, and it hid the real structure: the cube's weights come in pairs (the series of `tanh` and `coth`). Following this, flight 9 proved that the general statement it had been chasing was false, and proved the true one.

By the pilot of flight 9's own count — not checked line by line — there were about 27 distinct images over the nine flights. About 20 served, and at least 9 have the exact shape of a theorem. Others were decorative, and one served only to kill a candidate. One image, the turned lid, gave a symmetry that is measured and not proved: open question 2 of the paper.

## What failed

The record keeps every failure at the same size as the successes. A few of them:

- **The auditor's own formula.** He fitted a formula to dimensions 2 to 13, sealed its prediction for dimension 14 (`3368`), and it hit. The pencil then gave a different formula, which agrees up to 14 and differs at 15 by one unit. He sealed that too, against his own fit, and ran dimensions 15 and 16: **6436 and 12872**. The fit that had just hit was false. Thirteen agreeing cells had been a coincidence of small numbers.
- **«One binary digit per layer»**: right in dimensions 8 and 9, false in 10.
- **Conjecture B″** of an auditor about the fold law: flight 8 found a counterexample, a lattice of dimension 18.
- **The general cleanliness statement (R_gen)** that flight 9 set out to prove: flight 9 showed it is false, and proved the restricted statement that the cube needs.
- **«The mirror needs the whole roof»** (flight 7): too strong. Its counterexamples were all missing one ingredient, a mod-2 condition that the next auditor isolated.
- **The gap of version 1** (Lemma 7.2(b)), found by the third cold reader.
- **Sealed predictions that failed.** Dozens, published as they failed; the auditor's own include «there is no dry corner», «the prize decreases strictly», and «the weight at `m = 4` will bite».

## The numbers

Counted in the working folder of the project when version 8 was published, each file counted once by content.

| | |
|---|---|
| Flights (constructors), each audited | **9** |
| Cold readings | **10**: 2 of the chains of proof, 8 of the text |
| Versions of the paper | **8**; one gap found and repaired (version 2); no numbered statement changed after version 3 |
| Distinct files in the project | **2,638** — 337 Markdown documents, 427 Python engines, 1,055 logs |
| Logs ending with the watchdog's «finished» line | **1,017** of 1,055 |
| Hand-over files written after every turn, so that a new auditor could take over | **46** |
| Images given by the author, by the pilot of flight 9's count | about **27**; about **20** served |

---

[README](README.md) · [The theorems](THEOREMS.md) · [The record](record/README.md)
