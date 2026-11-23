# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning.

## Unreleased

### Added

- `Singularity/Scheme/NormalDimOne.lean`: `isRegularScheme_of_isIntegrallyClosed_stalk`. Let $X$ be a locally Noetherian scheme of dimension at most 1. If each local ring of $X$ is an integrally closed domain, then $X$ is regular. Mathlib has no class for normal schemes, so the hypothesis is written on the local rings.
- `Singularity/Algebra/Normalization.lean`: `finite_integralClosure_of_finite`. Let $P \to A$ be a finite injective map of domains, with $P$ Noetherian and integrally closed, and with $\operatorname{Frac} A$ separable over $\operatorname{Frac} P$. Then the integral closure of $A$ is a finite $A$-module. The corollary `finite_integralClosure_of_charZero` gives the finiteness of the normalization of each finitely generated domain over a field of characteristic 0. The case of characteristic $p$ is still open in Lean.

## 0.2.1 - 2026-11-24

### Added

- `Singularity/Algebra/Regular.lean`: the first facts about regular local rings. If $x \in \mathfrak{m} \setminus \mathfrak{m}^2$, then $R/(x)$ is regular of dimension $\dim R - 1$. A regular local ring is a domain. A Noetherian local domain of dimension 1 is regular if and only if it is a discrete valuation ring, and if and only if it is integrally closed. Sections 1 to 4 are adapted from resolutionorg/hironaka with attribution.

## 0.2.0 - 2026-11-23

### Added

- The workflow `trust`. Each week, and on request, it replays each declaration of `Singularity` and of `SingularityBase` in a fresh environment with `leanchecker` of the toolchain. This is a part of check Q3. `leanchecker` uses the kernel of Lean itself, thus it is not an independent kernel.
- `Singularity/Hypotheses/Integral.lean`: `IntegralResolutionInDim p n`, the main statement for integral varieties, and the named hypothesis `ReductionToIntegral`, the step from integral varieties to reduced varieties. The hypothesis is a `def ... : Prop`, not an axiom.
- The package `base/` (`SingularityBase`). It depends on resolutionorg/hironaka at the pin in `manifests/base.yaml` and proves `Singularity.Base.integralResolutionInDim_zero`: each integral variety over a field of characteristic 0 has a resolution. The proof applies Main Theorem I of the base and proves that the exceptional divisor of the blowup has a dense complement.
- `Singularity.resolutionInDim_zero`: resolution in characteristic 0 in each dimension, under the hypothesis `ReductionToIntegral`.
- `Singularity/Bridge/FormalConjectures.lean`: a copy of the definition `Scheme.HasResolution` of google-deepmind/formal-conjectures, and its statements `FCResolutionInDim p n` and `FCResolutionCharZero` as propositions.
- `base/SingularityBase/Bridge.lean`: `hasResolution_of_isResolution`, a resolution of an integral variety over a perfect field in the sense of the project is a resolution in the sense of formal-conjectures. Also `fcResolutionInDim_of_resolutionInDim` and `fcResolutionCharZero`, the statement `resolution_of_singularities_of_charZero` of formal-conjectures with no named hypothesis.
- The workflow `base`, which builds the base package and keeps the build of resolutionorg/hironaka in an actions cache.

### Changed

- `scripts/Export.lean` accepts the root module as an optional fourth argument.
- `scripts/scan.sh` also scans `base/`.

## 0.1.0 - 2026-11-23

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
