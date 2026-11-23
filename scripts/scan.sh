#!/bin/sh
# Scan the main tree for the escape hatches of spec 09.2: sorry, admit, a new axiom, native_decide, implemented_by and @[extern]. The scan includes the package in base/. Singularity/WIP is not scanned, because it is not imported by Singularity.lean. The script prints each hit and exits with code 1 when it finds one.
set -eu
hits=$(grep -rnE '\bsorry\b|\badmit\b|^[[:space:]]*(private |protected )?axiom |native_decide|implemented_by|@\[extern' Singularity Singularity.lean base/SingularityBase base/SingularityBase.lean --include='*.lean' | grep -v '^Singularity/WIP/' | grep -vE ':[0-9]+:[[:space:]]*(--|/-|\*)' || true)
if [ -n "$hits" ]; then
  echo "$hits"
  echo "the main tree has an escape hatch; move the proof to Singularity/WIP"
  exit 1
fi
echo "the main tree has no escape hatch"
