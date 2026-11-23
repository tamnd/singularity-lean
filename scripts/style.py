#!/usr/bin/env python3
"""Check the writing rules of the project on Markdown and YAML text.

The rules are:
1. No em dash and no en dash.
2. No line break in the middle of a sentence. A line of a paragraph must not continue on the next line.
3. No page break (a form feed or a LaTeX page break command).

The YAML front matter of a Markdown file is checked for rules 1 and 3 only.

The script prints each fault as path:line: message and exits with code 1 when it finds a fault.
"""

import pathlib
import re
import sys

DASHES = {"\u2014": "em dash", "\u2013": "en dash"}
PAGEBREAK = re.compile(r"\\(newpage|clearpage|pagebreak)\b|\f")
BLOCK = re.compile(r"^\s*(#|[-*+] |\d+\. |\||>|<|```|~~~|\$\$|---$|- \[|!\[)")


def check(path: pathlib.Path) -> list[str]:
    faults = []
    lines = path.read_text(encoding="utf-8").split("\n")
    fence = False
    front = 0
    if path.suffix == ".md" and lines and lines[0] == "---":
        front = next((j for j in range(1, len(lines)) if lines[j] == "---"), 0) + 1
    for i, line in enumerate(lines, 1):
        for ch, name in DASHES.items():
            if ch in line:
                faults.append(f"{path}:{i}: {name}")
        if PAGEBREAK.search(line):
            faults.append(f"{path}:{i}: page break")
        if path.suffix != ".md" or i <= front:
            continue
        if line.lstrip().startswith(("```", "~~~")):
            fence = not fence
            continue
        if fence or not line.strip() or BLOCK.match(line) or line.startswith("    "):
            continue
        if i < len(lines):
            nxt = lines[i]
            if nxt.strip() and not BLOCK.match(nxt) and not nxt.startswith("    ") and not line.rstrip().endswith(("  ", "\\")):
                faults.append(f"{path}:{i}: the paragraph continues on the next line")
    return faults


def main(argv: list[str]) -> int:
    roots = [pathlib.Path(a) for a in argv] or [pathlib.Path(".")]
    faults = []
    for root in roots:
        files = [root] if root.is_file() else sorted(root.rglob("*"))
        for f in files:
            if f.suffix in (".md", ".yaml", ".yml") and ".git" not in f.parts and "node_modules" not in f.parts:
                faults += check(f)
    for f in faults:
        print(f)
    return 1 if faults else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
