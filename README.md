# singularity-lean

The Lean 4 code of the singularity project. The project states resolution of singularities in characteristic $p > 0$ in Lean, formalizes the known cases, and works on the open case: varieties of dimension 4 and higher.

**The open case is not proved.** This package has the statements of the open problem and the first fidelity checks of the statements. It does not have a proof of the open case.

The map of the project, the milestones and the site are in [tamnd/singularity](https://github.com/tamnd/singularity). The site is [singularity.tamnd.com](https://singularity.tamnd.com). The `sing` command that reads the records of this package is in [tamnd/singularity-agent](https://github.com/tamnd/singularity-agent).

## What is here

| File | Content |
|---|---|
| `Singularity/Statements/Basic.lean` | the vocabulary: `regularLocus`, `IsRegularScheme`, `IsResolution` and `IsVariety` |
| `Singularity/Statements/Main.lean` | `ResolutionInDim`, `ResolutionOfSingularities` and `ResolutionDimFourCharP` |
| `Singularity/Statements/Core.lean` | the purely inseparable hypersurfaces $z^p + g = 0$, the core case of route R5 |
| `Singularity/Fidelity/Positive.lean` | check F2: the identity of a regular scheme is a resolution |
| `Singularity/Known/DimZero.lean` | `resolutionInDim_dim_zero`, resolution in dimension 0 in each characteristic |
| `scripts/Export.lean` | writes the record of the build: each declaration, its type and its axioms |

The statements use "regular" and not "smooth over $k$". Over an imperfect field a regular variety need not be smooth, so the statement with "smooth" is false there.

## Build

The package uses Lean `v4.35.0` and Mathlib `v4.35.0`. This is the pin of resolutionorg/hironaka, the base of the project in characteristic 0.

```sh
lake exe cache get
lake build
```

To write the record of the build:

```sh
lake env lean --run scripts/Export.lean "$(git rev-parse HEAD)" v4.35.0 "$(date -u +%Y-%m-%d)" > records/lean.json
python3 scripts/axioms.py records/lean.json
```

## Rules

1. No `sorry`, `admit`, `axiom` or `native_decide` in the main tree. Work that is not finished goes in `Singularity/WIP/`, which `Singularity.lean` does not import. The script `scripts/scan.sh` checks this.
2. A published theorem that is not formalized yet is a `def ... : Prop` and a hypothesis of the theorems that use it. It is never an `axiom`.
3. The files of `Singularity/Statements/` are pinned by hash in `manifests/statements.sha256`. A change to a statement must change the hash in the same pull request.

## Licence

Apache-2.0. Refer to `LICENSE`.
