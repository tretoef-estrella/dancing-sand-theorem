#!/bin/zsh
cd /Users/rafa/Desktop/ARBOLYAML/HYPERCUBE/lean/proyecto_cubo
V=/Users/rafa/Desktop/ARBOLYAML/corpus4/herramientas_grepy/vigia.sh
OUT=/Users/rafa/Desktop/ARBOLYAML/HYPERCUBE/logs/buildC22.log
: > $OUT
for M in Sum Basic L1Defs L1Comm PartL1 PartL2 PartL3 All; do
  echo "=== MODULE $M $(date '+%H:%M:%S')" >> $OUT
  L=/Users/rafa/Desktop/ARBOLYAML/HYPERCUBE/logs/buildC22_$M.log
  TOPE_KB=4718592 TOPE_S=900 zsh $V $L "lake build RequestProject.Lemma35.$M"
  echo "vigia_rc=$?" >> $OUT
  tail -n 3 $L >> $OUT
  if ! tail -n 1 $L | grep -q 'VIGIA-FIN-OK exit=0'; then echo "BUILD-LOOP-STOPPED at $M" >> $OUT; exit 1; fi
done
echo BUILD-LOOP-END >> $OUT
