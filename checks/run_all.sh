#!/bin/zsh
# run_all.sh — runs every check of §12.1 of «The Dancing Sand Theorem», each under the watchdog vigia.sh
# (caps 1.2 GB of memory and 600 s per run). Run from this folder:  zsh run_all.sh
# Each log in logs/ counts only if its last line begins with VIGIA-FIN-OK.
cd ${0:A:h}
run() { local name=$1; shift; zsh vigia.sh logs/$name.log "$*"; tail -1 logs/$name.log | sed "s/^/$name: /"; }
run gate_direct_11        'python3 gate/gate_direct.py 11'
run gate_dance_40_6       'python3 gate/gate_dance.py 40 6'
run gate_sections5to7_127_3 'python3 gate/gate_sections5to7.py 127 3'
run gate_strict_cut_6_4   'python3 gate/gate_strict_cut.py 6 4'
run gate_lemma72_9_20000  'python3 gate/gate_lemma72.py 9 20000'
run gate_theoremO_5       'python3 gate/gate_theoremO.py 5'
run gate_section9_200     'python3 gate/gate_section9.py 200'
run gate_section10_22_5   'python3 gate/gate_section10.py 22 5'
run remark2_generic_rand  'cd gate/remark2 && python3 gate_remark2.py generic rand 11'
run remark2_generic_eta   'cd gate/remark2 && python3 gate_remark2.py generic eta 11'
run remark2_oddU_rand     'cd gate/remark2 && python3 gate_remark2.py oddU rand 11'
run remark2_oddU_eta      'cd gate/remark2 && python3 gate_remark2.py oddU eta 11'
