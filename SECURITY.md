# Security

This package is Lean code with no network access and no secrets. The security risk is a proof that Lean accepts but that does not prove what it claims. Examples are a hidden axiom, a `native_decide`, or a statement that does not mean what its docstring says.

If you find such a problem, open an issue in [tamnd/singularity](https://github.com/tamnd/singularity/issues) with the label `gap`. If the problem is in a workflow or in a dependency, use the private reporting of GitHub security advisories of this repository.
