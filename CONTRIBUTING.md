# Contributing

Thank you for your help. Read this file before you open a pull request.

## Before you start

1. Find the node of the map that your work is for. The nodes are in `blueprint/nodes/` of [tamnd/singularity](https://github.com/tamnd/singularity). Each node names the Lean declaration that it needs.
2. Find the milestone issue of the node in [the issues of tamnd/singularity](https://github.com/tamnd/singularity/issues).

## The pull request

1. Use Mathlib style and Mathlib names.
2. Give each definition and each theorem a docstring. In a statement file, the docstring has the informal statement and a reference.
3. Do not put `sorry`, `admit` or `axiom` in the main tree. Put unfinished work in `Singularity/WIP/`.
4. Run `lake build` and `sh scripts/scan.sh` before you push.
5. Write "Refers to tamnd/singularity#N" in the description, with the number of the milestone issue.
6. Give the pull request one `area/*` label and one `type/*` label.

## Statements

A change to a file of `Singularity/Statements/` changes the meaning of the project. Such a change needs the label `type/statement`, a new line in `manifests/statements.sha256`, and a reason in the description.

## Writing

Write in plain technical English. Use short sentences. Do not use an em dash. Do not break a line in the middle of a sentence in Markdown.
