# Sealed predictions of the auditor for the audit of flight 8 (written 2026-10-04 21:36:41, BEFORE the runs)
- A8.1 (95 %): my independent engine (gh_audit_vuelo7.py mode S: H-odd/H-even half-size Smith, my own rule) finds 0 failures on every sampled cell of n = 101..144 with half-dim <= 128.
- A8.2 (90 %): the six *_chk logs of flight 8 all end VIGIA-FIN-OK, report 0 failures and 0 pivot failures, and their cell counts sum to 5 254.
- A8.3 (85 %): fdance.py contains an explicit pivot-integrality assertion that makes a non-unit pivot a failure (not a silent pass).
- A8.4 (70 %): the B″ lattice of §0 (dim 18) reproduced by the flight's verify_break gives X̄ = {1³,3,8,11} and 2X = {1²,2²,8,11} at i = 1 (their code path; my independent check is separate).
- A8.5 (90 %, written 2026-10-04 21:53:56 before the runs): single-n runs at half-dim <= 512, n = 104, 116, 128, 144, each 0 failures.
