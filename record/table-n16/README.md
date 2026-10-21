# The table of §1.9: `Syl_2 K(Q_n)` for `n ≤ 16`

Version 12 of the paper (21 October 2026) adds §1.9, a table of the 2-part of the sandpile group of `Q_n` for `n = 2, …, 16`, computed by the rule of §1.2. It adds no statement and was not read cold. This folder holds the logs that check its rows.

| file | what it is |
|---|---|
| `paper_rule_abs_2_16.log` | the rows, from the paper's `gate/rule_abs.py` (the table in the paper is generated from this log, no row typed by hand) |
| `second_route.py`, `second_route.log` | a second program for the rule — the first cold reader's own engine (`../cold-readings/01-the-chain-of-the-main-theorem/engines/myrule.py`, written without our code), in both of its forms — against the log above: 30/30 rows equal; the control «no pooling» differs in 4 rows, as it must |
| `gh_bai_table_gate_v2.log` | rows 2–11 against Bai's printed table [Bai03, p. 260]: 10/10; the control (a lowered rule) matches 0 |
| `large_n.log` | the rule at `n = 40, 64, 100`: time and Bai's two counts |
| `gh_audit_vuelo1.log` | rows 2–13 against the 2-adic Smith form of the Laplacian of `Q_n` computed directly («PASS full»); rows 14–16: the numbers of cyclic factors of order `2`, of order `4` and of order at least `8`, computed by linear algebra over `𝔽_2` without the rule («PASS layers»; the third number counts the summand `ℤ_2` of the Main Theorem, hence `+1`); the control (a perturbed rule) fails in 8 cells |

In every row the number of cyclic factors is `2^{n−1} − 1` and the number of factors `ℤ/2` is `2^{n−2} − 2^{⌊(n−2)/2⌋}` (Corollary 1.5, Bai's counts). Rows 14–16 were not compared with a direct Smith form. By Theorem DW, the group of the folded cube is the same row with every exponent lowered by one and the entry `1` removed (the third column of the table in the [README](../../README.md)).

The rule computes much larger rows in a fraction of a second (`n = 40, 64, 100` take at most 0.01 s each, `large_n.log`); what is expensive is checking a row against a direct Smith form, and the record stops at `n = 13`.
