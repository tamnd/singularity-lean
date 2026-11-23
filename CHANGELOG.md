# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

### Added

- The statements of the problem: `regularLocus`, `IsRegularScheme`, `IsResolution`, `IsVariety`, `ResolutionInDim`, `ResolutionOfSingularities`, `ResolutionDimFourCharP` and `PurelyInseparableHypersurfaceResolution`.
- Fidelity check F2: `isResolution_id`, the identity of a regular scheme is a resolution.
- Fidelity check F3: `not_isResolution_codiag`, the codiagonal $X \sqcup X \to X$ is not a resolution when $X$ has a regular point.
- `scripts/Export.lean`, which writes the record of the build, and `scripts/axioms.py`, which checks the axioms in the record.
- `scripts/scan.sh`, which finds `sorry`, `admit`, `axiom` and `native_decide` in the main tree.
- The workflows `build`, `check` and `scorecard`.
- `formalization.yaml`, the metadata of the formalization, and `manifests/statements.sha256`, the hashes of the statement files.
