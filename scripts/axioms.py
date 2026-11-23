#!/usr/bin/env python3
"""Check the axioms in a record of the Lean build.

The record is the JSON that scripts/Export.lean writes. Each declaration of the main tree must use only the standard axioms propext, Classical.choice and Quot.sound. The script prints each declaration that uses another axiom, and exits with code 1 when it finds one.
"""

import json
import sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def main(path):
    with open(path, encoding="utf-8") as f:
        rec = json.load(f)
    bad = []
    for name, d in sorted(rec["decls"].items()):
        other = sorted(set(d.get("axioms", [])) - STANDARD)
        if other:
            bad.append(f"{name}: {', '.join(other)}")
    for b in bad:
        print(b)
    print(f"{len(rec['decls'])} declarations, {len(bad)} with an axiom that is not standard")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
