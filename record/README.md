# The record

This folder holds the record of how the proofs of [the paper](../paper/THE_DANCING_SAND_THEOREM_v8.pdf) were found and checked. It is a selection: the documents needed to see who checked what, with which code, and what each reader found. They are working documents, not refereed, mostly in English, with some passages in Spanish (the author's words are kept verbatim). **Where they differ from the paper, the paper is authoritative.**

The roles are described in [THE_STORY_AND_THE_NUMBERS.md](../THE_STORY_AND_THE_NUMBERS.md):
- the **constructors** found the proofs, one «flight» each;
- the **auditors** re-derived them with their own code;
- the **cold readers** read the chains and the text with no access to the audits.

All of them were instances of Claude (Anthropic).

## Cold readings — [cold-readings/](cold-readings/)

Each folder holds four kinds of file:
- `MISSION.md`, what the reader was given and told, as written;
- `REPORT.md`, its report;
- the reader's own code and logs (`checks/`, `engines/`, `logs/`, `scratch/`);
- `GRADING.md`, the author's grading of the reading. The auditor checked every claim of the report and re-ran a sample of its code.

Scratch files that are not code are left out: page images, HTML renderings and temporary files. So are the papers of other authors that the readers read.

| | What was read | Verdict | Grading |
|---|---|---|---|
| [01](cold-readings/01-the-chain-of-the-main-theorem/REPORT.md) | the chain of the Main Theorem, from the statements and the flights' reports | **holds**, every link re-derived; one constant of a one-line statement in the mission corrected | high mark |
| [02](cold-readings/02-the-chain-of-the-fold-law/REPORT.md) | the chain of the fold law | **holds** | highest mark |
| [03](cold-readings/03-paper-v1-whole/REPORT.md) | version 1 of the paper, whole, as a referee | **holds with gaps**: Lemma 7.2(b) false as stated, repair proposed; no theorem affected | highest mark |
| [04](cold-readings/04-changes-of-v2/REPORT.md) | the changes of version 2: the repair | **the repair holds**; Lemma 7.9 strengthened to integrality | highest mark |
| [05](cold-readings/05-changes-of-v3/REPORT.md) | the changes of version 3, and the PDF | the changes hold; the PDF has defects of typesetting | second look by the auditor |
| [06](cold-readings/06-changes-of-v4/REPORT.md) | the changes of version 4, and the PDF | no gap or error in the mathematics; gaps in the record | highest mark |
| [07](cold-readings/07-changes-of-v5/REPORT.md) | the changes of version 5, and the PDF | the mathematics of the changes holds; the PDF is not yet right | highest mark |
| [08](cold-readings/08-v6-whole-for-correctness/REPORT.md) | version 6, whole, for correctness | **holds**; four defects of the record, none in the mathematics | highest mark |
| [09](cold-readings/09-changes-of-v7/REPORT.md) | the changes of version 7 | the mathematics holds; one false sentence of the record | highest mark |
| [10](cold-readings/10-v8-final/REPORT.md) | the changes of version 8 | nothing mathematical changed; one false clause, replaced word for word | highest mark |

Readers 1 to 6 are the readers 1 to 6 of §12.2 of the paper; their code is the code behind its rows.

**One redaction.** In [05/GRADING.md](cold-readings/05-changes-of-v3/GRADING.md), line 11 named a private note of the author among the files read. That name was replaced by «[a private note of the author, not published — redacted in this copy]». Nothing else in this folder was changed.

## Flights — [flights/](flights/)

Each folder holds:
- `MISSION.md`, as written;
- `REPORT.md`, the constructor's report, with its sealed predictions and its failures;
- `AUDIT.md`, the auditor's audit;
- where it exists, `AUDITOR_SEALED_PREDICTIONS.md`, the predictions the auditor sealed before reading the report.

The constructors' engines and logs are not included. The audits name them, and they are kept by the author.

| Flight | What it brought |
|---|---|
| [1](flights/flight-1/REPORT.md) | the splitting over tilting modules; a closed rule, as a conjecture |
| [2](flights/flight-2/REPORT.md) | the doubling functor `Φ`; the dance (Theorem D) |
| [3](flights/flight-3/REPORT.md) | the unique cheapest matching (Theorem O) |
| [4](flights/flight-4/REPORT.md) | the floor (Theorem F): the rule for every `n` |
| [5](flights/flight-5/REPORT.md) | the podium: Gao et al.'s Conjecture 4.14 and the `(n+1)`-th factor |
| [6](flights/flight-6/REPORT.md) | Gao et al.'s Conjecture 5.4; the fold law up to `n = 21` |
| [7](flights/flight-7/REPORT.md) | the fold law for every `n ≤ 100` |
| [8](flights/flight-8/REPORT.md) | the mod-2 layer of the fold law for every `n`; the fold law for every `n ≤ 144`; an auditor's conjecture refuted |
| [9](flights/flight-9/REPORT.md) | Lemma Ω: the fold law for every `n` |

[THE_FOLD_LAW_PENCIL_NOTE.md](flights/THE_FOLD_LAW_PENCIL_NOTE.md) is the note in which the fold law was first stated, with the pencil proofs of its first two layers; [COLD_AUDIT_FOLD_LAW.md](flights/COLD_AUDIT_FOLD_LAW.md) is its second reading, by the auditor.

## Corrections — [corrections/](corrections/)

What changed from each version of the paper to the next, with the source of each change: the report that asked for it, or the auditor's own finding. The Markdown of versions 1 to 7 is in [../paper/earlier-versions/](../paper/earlier-versions/), so every quotation in a report can be found in the version it quotes.

## Literature — [literature/](literature/)

- [LITERATURE_SWEEP.md](literature/LITERATURE_SWEEP.md): the search behind §1.8 of the paper. It holds the query log, the sources read in the original, and the verdict on each claim (ours, others', shared).
- [SWEEP_NOVELTY_OF_THEOREM_D.md](literature/SWEEP_NOVELTY_OF_THEOREM_D.md): the search for an earlier tilting decomposition of a sandpile group. None was found.
- [BAI_2003_READ_IN_THE_ORIGINAL.md](literature/BAI_2003_READ_IN_THE_ORIGINAL.md): Bai's paper, read in the original.

---

[README](../README.md) · [The story and the numbers](../THE_STORY_AND_THE_NUMBERS.md)
