#!/bin/zsh
# clean_rebuild_cubo.sh — Grepy Escribano, 10 Oct 2026 (modelled on the Chaise's clean_rebuild_pares.sh).
# Clean rebuild of the WHOLE Lean project of «The Dancing Sand Theorem»: the project's own build
# directory is moved aside (Mathlib in .lake/packages untouched) and every module is rebuilt one at a
# time, in topological order (orden_modulos.txt, 416 modules = 415 + Main), each with its own
# `lake build` under the watchdog with the Lean cap (Rafa's OK of 30 Sep: 4.5 GB real footprint,
# 900 s per module).
# RESUMABLE: if the backup directory already exists the build directory is not moved again, and every
# module whose own log already ends in `VIGIA-FIN-OK exit=0` is skipped.
# STOPS at the first failure (its dependents would fail too); fix, then rerun this script.
# Estimate written before launching: sum of the last build time of each module = 42 556 s (11.8 h),
# plus ~10-20 s of lake start-up per module (~1.5 h): about 12-14 h. Peak per module 2.33 GB
# (largest earlier build). Longest earlier module 293 s (Lemma35.L1Comm), well under 900 s.
P=/Users/rafa/Desktop/ARBOLYAML/HYPERCUBE/lean/proyecto_cubo
D=/Users/rafa/Desktop/ARBOLYAML/HYPERCUBE/lean/clean_rebuild
V=/Users/rafa/Desktop/ARBOLYAML/corpus4/herramientas_grepy/vigia.sh
LOG=$D/clean_rebuild_2026-10-10.log
BK=.lake/build_pre_clean_2026-10-10
mkdir -p $D/cr_logs
cd $P || exit 1
if [ -e $BK ]; then
  echo "RESUME $(date '+%Y-%m-%d %H:%M:%S')" >> $LOG
else
  mv .lake/build $BK || exit 1
  echo "START $(date '+%Y-%m-%d %H:%M:%S')" >> $LOG
fi
n=0; skipped=0
while read mod; do
  case "$mod" in '#'*) echo "SKIPPED ${mod#\#}" >> $LOG; continue;; esac
  L=$D/cr_logs/$mod.log
  if [ -f $L ] && tail -n 1 $L | grep -q 'VIGIA-FIN-OK exit=0'; then skipped=$((skipped+1)); continue; fi
  n=$((n+1)); s=$(date +%s)
  TOPE_KB=4718592 TOPE_S=900 zsh $V $L "lake build $mod"
  last=$(tail -n 1 $L)
  echo "$mod $last wall=$(( $(date +%s) - s ))s" >> $LOG
  case "$last" in *'VIGIA-FIN-OK exit=0'*) ;; *)
    echo "STOP at $mod $(date '+%Y-%m-%d %H:%M:%S') built_this_run=$n skipped_done=$skipped" >> $LOG
    echo FIN-FAIL >> $LOG; exit 1;;
  esac
done < $D/orden_modulos.txt
echo "END $(date '+%Y-%m-%d %H:%M:%S') built_this_run=$n skipped_done=$skipped" >> $LOG
echo FIN-OK >> $LOG
