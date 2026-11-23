# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

### Added

- The statements of the problem: `regularLocus`, `IsRegularScheme`, `IsResolution`, `IsVariety`, `ResolutionInDim`, `ResolutionOfSingularities`, `ResolutionDimFourCharP` and `PurelyInseparableHypersurfaceResolution`.
- Fidelity check F2: `isResolution_id`, the identity of a regular scheme is a resolution.
- Fidelity check F3: `not_isResolution_codiag`, the codiagonal $X \sqcup X \to X$ is not a resolution when $X$ has a regular point.
- Fidelity of the core problem: `purelyInseparableHypersurfaceResolution_of_resolutionInDim`, P1 is a special case of `ResolutionInDim p n` for $p \neq 0$. The proof shows that the hypersurface $z^p + g = 0$ has dimension at most $n$ and is a variety when it is reduced.
- `resolutionInDim_dim_zero`: each variety of dimension at most 0 has a resolution, in each characteristic. A reduced scheme of dimension at most 0 is regular, so the identity is a resolution.
- `scripts/Export.lean`, which writes the record of the build, and `scripts/axioms.py`, which checks the axioms in the record.
- `scripts/scan.sh`, which finds `sorry`, `admit`, `axiom` and `native_decide` in the main tree.
- The workflows `build`, `check` and `scorecard`.
- `formalization.yaml`, the metadata of the formalization, and `manifests/statements.sha256`, the hashes of the statement files.
