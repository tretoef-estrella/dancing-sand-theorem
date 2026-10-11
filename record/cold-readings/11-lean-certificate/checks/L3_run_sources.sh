#!/bin/zsh
# Re-elaborate project source files one at a time, each under the watchdog with the Lean cap.
cd ${0:a:h}/../material/project
for f in "$@"; do
  tag=${${f#RequestProject/}//\//_}; tag=${tag%.lean}
  TOPE_KB=4718592 TOPE_S=900 zsh ../../vigia.sh ../../checks/L3_src_$tag.log "lake env lean $f"
  print "$f: $(tail -1 ../../checks/L3_src_$tag.log)  errors=$(grep -c 'error' ../../checks/L3_src_$tag.log)"
done
