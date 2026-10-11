# Version 9 of «The Dancing Sand Theorem»: the Lean certificate (plan A-D of 11 Oct 2026, step B1; Grepy Escribano).
# Built from version 8 by anchored edits; every replacement is asserted unique. No statement and no number of the
# mathematics changes. One sentence of §1.3 is corrected (cold reading of the Lean certificate, finding F-ERR-4).
# No sentence describes the paper's own versions (notes/DIAGNOSTICO_EL_BUCLE_DE_LAS_VERSIONES_v1.md), except the
# version label of the header. The Zenodo DOI of the Lean certificate is not known yet: one placeholder [LC-DOI].
import sys
SRC = 'material/paper/THE_DANCING_SAND_THEOREM_v8.md'
DST = 'scratch/v9_by_text_edits.md'
s = open(SRC, encoding='utf-8').read()

def rep(old, new, label):
    global s
    n = s.count(old)
    assert n == 1, (label, n)
    s = s.replace(old, new, 1)
    print('ok', label)

# E1. header
rep('6 October 2026 · version 8', '11 October 2026 · version 9', 'E1 header')

# E2. abstract
rep('its whole sandpile group. This work has not been refereed by a human expert.',
    'its whole sandpile group. **The whole proof has been checked in the proof assistant Lean 4 with the Mathlib library, with nothing cited.** This work has not been refereed by a human expert.',
    'E2 abstract')

# E3. (none: a «Lean» column made the table wider than the page and Chrome scaled every page; the Lean names are in §12.3)

# E4. §1.0 paragraph: one sentence
rep('(Appendix A). No human expert has refereed this work. The words of our own',
    '(Appendix A). The whole proof has also been checked in Lean 4 with Mathlib, with nothing cited, and that check was read cold before release; the Lean name of each result of the table is in §12.3. No human expert has refereed this work. The words of our own',
    'E4 §1.0 sentence')

# E5. §1.3: the folded cube (cold reading of the Lean certificate, F-ERR-4)
rep('its vertices are the `2^{n−1}` pairs of antipodal words, and two pairs are joined once for each pair of words, one from each, that differ in one letter.',
    'its vertices are the `2^{n−1}` pairs `{x, x + 𝟙}` of antipodal words, and `{x, x + 𝟙}` is joined to `{x + e_i, x + 𝟙 + e_i}` once for each `i = 1, …, n`, where `e_i` is the `i`-th unit vector; each edge of `Q_n/⟨𝟙⟩` is the image of two edges of `Q_n`.',
    'E5 §1.3')

# E6. §11, question 6
rep('6. **Formal verification.** No part of this paper has been checked by a proof assistant. The dance (§4, §10.3) and the valuation arguments (§5–§7) are finite and explicit, and seem suited to it.',
    '6. **The tilting modules in Lean.** Every theorem of this paper is checked in Lean (§12.3), with the dance lattices `T(λ)` of §3.3 as explicit lattices. That they are the indecomposable tilting modules of `SL_2` in characteristic `2` is not formalized, and the proof does not need it. Formalizing it would join the formal proof to the representation theory that guided it.',
    'E6 §11 Q6')

# E7. §12.3, new subsection, before §13
sub = '''### 12.3 The Lean certificate

Every theorem of this paper has been checked in the proof assistant Lean 4 [dMU21], toolchain `v4.28.0`, with the Mathlib library [mC20], tag `v4.28.0`. The certificate [LC26] prints the Lean statements and every definition they use, compares them with this paper line by line, and says how the proof was obtained and how to check it. Piece numbers such as C15 refer to its §3.

**What Lean proves.** For every `n ≥ 1`:
- the Main Theorem (`MainTheorem.M1`), with the rule of §1.2 written out in Lean: the recursion for the multiplicities, the binary digits of `λ + 1`, the raw clocks, the integer antitonic fit and the groups `X(λ, i)`;
- Theorem DW (`FoldLaw.DW`) and, for `n ≥ 2`, its equivalent form (`FoldLaw.DW'`);
- Corollary 1.4: the odd part (`OddParts.C5`); the `2`-part is `FoldLaw.DW'` read together with the Main Theorem, which Lean does not state as one theorem;
- Corollaries 1.5 (`BaiCounts.B1`, `BaiCounts.B2`), 1.6 (`PodiumCor.P1`, `PodiumCor.P2`, `PodiumCor.P3`, `PodiumCor.G1`, `PodiumCor.G2`, `PodiumCor.G3`; Gao et al.'s Theorem 4.1 for `n ≥ 3`) and 1.7 (`Mirror.Y2`);
- Bai's odd part of `K(Q_n)` (`OddParts.B1`), which this paper cites [Bai03] and Lean proves;
- Theorem D (`Windows.theorem_D_i`), and each of the 68 numbered statements of §2–§10, from Lemma 2.1 to Theorem 10.22.

**Nothing is cited.** The statements are about a finite graph. Lean defines the Laplacian of `Q_n`, its cokernel and the torsion of that cokernel, and proves the theorems themselves; Kirchhoff's theorem is not used. The proof contains no `sorry`, and every theorem depends only on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`.

**The one point of trust** is that the Lean definitions say what this paper says. The certificate prints every definition the statements use and compares it with this paper (its §1.2–§1.3). That comparison is what a reader should check.

**How.** The text of §2–§10 was cut into 68 pieces, each a short self-contained file. Aristotle, an AI system made by Harmonic [Har26], wrote the Lean proofs. On the author's machine each returned project was compared with the previous one, searched for forbidden constructs, and compiled module by module; the main statements of each piece were restated by hand in a check file, and their faithfulness to the paper was audited. At the end all 416 modules were compiled again from their sources, in one clean rebuild, all with exit code 0. The project has 415 Lean files, 60 940 lines and 3 449 theorem and lemma declarations.

**Read cold.** Before release, the certificate was read by a reader other than its writer, with the compiled project at hand. The reader re-read every definition in the statements against this paper, re-elaborated from source the files of the Main Theorem and of Theorem DW and five more of the chain, and compared the rule with Smith forms it computed from the graphs (`n ≤ 11`). Verdict: «holds as far as I can check»; no Lean statement says something other than this paper. It found four errors in the certificate's own record (three counts and one sentence) and none in a statement; they are corrected in [LC26].

**What Lean does not state** ([LC26], §2):
- the pool-adjacent-violators algorithm (Lean has the fit it computes);
- that the dance lattices are the indecomposable tilting modules (not used);
- the equivalent form of Theorem DW at `n = 1`, where both groups are trivial, and Gao et al.'s Theorem 4.1 at `n = 2`, where `K(Q_2) = ℤ/4`;
- the numerical facts of §1.2, §1.3 and §12.

The Main Theorem is an isomorphism of groups in Lean and of `ℤ_2`-modules here. The two statements are equivalent, because an additive map between finitely generated `ℤ_2`-modules is `ℤ_2`-linear ([LC26], §1.3).

**Where.** The certificate [LC26] is published with the Lean project, the check files, the files of the 68 pieces, and the logs of every piece and of the clean rebuild.

## 13. Exact status'''
rep('## 13. Exact status', sub, 'E7 §12.3')

# E8. §13
rep('- **Not done:** a human referee; a formal verification.',
    '- **Checked in Lean 4 with Mathlib:** every result above and each numbered statement of §2–§10, with nothing cited; the certificate was read cold (§12.3).\n- **Not done:** a human referee.',
    'E8 §13 bullets')
rep('The results are stated as theorems because every step has a written proof that was re-derived by readers other than its author. That is not a substitute for refereeing.',
    'The results are stated as theorems because every step has a written proof that was re-derived by readers other than its author, and because the whole proof has been checked in Lean. Neither is a substitute for refereeing.',
    'E8 §13 closing')

# E9. Acknowledgements
rep('The author directed the project and takes responsibility for the content.',
    'The Lean proofs (§12.3) were written by Aristotle, an AI system made by Harmonic [Har26], from pieces written from this paper. Instances of Claude wrote the pieces, audited what came back, compiled it on the author\'s machine, and read the certificate cold.\n\nThe author directed the project and takes responsibility for the content.',
    'E9 acknowledgements')

# E10. Appendix A, one entry at the end
i = s.index('## Appendix A. How this work was done')
j = s.index('\n\n## References', i)
s = s[:j] + '\n\n**Formal verification.** From 6 to 10 October 2026 the proofs were checked in Lean 4 with Mathlib, in 68 pieces; the certificate was read cold on 11 October 2026 (§12.3, [LC26]).' + s[j:]
print('ok E10 appendix A')

# E11. References
rep('- [Hum72] J. E. Humphreys,', '- [Har26] Harmonic, Aristotle, an AI system for mathematics, https://aristotle.harmonic.fun (2026).\n- [Hum72] J. E. Humphreys,', 'E11 [Har26]')
rep('- [Don93] S. Donkin,', '- [dMU21] L. de Moura, S. Ullrich, The Lean 4 theorem prover and programming language, in *Automated Deduction — CADE 28*, Lecture Notes in Computer Science 12699, Springer, 2021, 625–635.\n- [Don93] S. Donkin,', 'E11 [dMU21]')
rep('- [Lor91] D. J. Lorenzini,', '- [LC26] R. Amichis Luengo, *The Dancing Sand Theorem — Lean certificate*, Zenodo (2026), DOI [LC-DOI].\n- [Lor91] D. J. Lorenzini,', 'E11 [LC26]')
rep('- [MGM19] J. Marx-Kuo,', '- [mC20] The mathlib Community, The Lean mathematical library, in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, 367–381.\n- [MGM19] J. Marx-Kuo,', 'E11 [mC20]')

open(DST, 'w', encoding='utf-8').write(s)
print('written', DST)
