This project was edited by [Aristotle](https://aristotle.harmonic.fun).

> **WIP / specification warning.** The current comparator theorem is a valid
> consequence of the public `IsAdmissible` and `worthiness` definitions, but it
> is not yet the intended Nesterenko-row theorem. Because the statement places
> no provenance restriction on `q` and `p`, elementary rounding proves the same
> `1-ε` bound for every real number. The structured Nesterenko proof still needs
> its exact special-value bridge and real asymptotic rates formalized.

## API documentation

Auto-generated with [doc-gen4](https://github.com/leanprover/doc-gen4) from the
nested `docbuild/` project (pinned to the same Lean toolchain):

```
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake build RequestProject:docs
```

Output lands in `docbuild/.lake/build/doc/`; serve it with
`python3 -m http.server` from that directory. On pushes to `main`, CI
(`.github/workflows/docs.yml`) builds the docs and deploys them to GitHub
Pages.

## Metadata

See [formalization.yaml](./formalization.yaml) for provenance, scope, axioms, and
review status, following the
[mathlib-initiative/formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml)
standard. Validate it with:

```
check-jsonschema --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json formalization.yaml
```

## Verifying the current WIP statement with comparator

The current regression theorem (`Catalan.catalan_worthiness_one_sub_eps_unconditional`,
`RequestProject/Unconditional.lean`) has no arithmetic or analytic hypotheses.
In fact, the same construction proves the `1-ε` statement for every real
number under the project's public `IsAdmissible` and `worthiness` definitions.
This exposes the specification gap described above. It can be checked with
[leanprover/comparator](https://github.com/leanprover/comparator):

* `Challenge.lean` states the theorem with a `sorry` placeholder;
* `Solution.lean` discharges the identical statement using the formalized proof;
* `comparator.config.json` is the comparator configuration (permitted axioms:
  `propext`, `Quot.sound`, `Classical.choice`).

To run the check you need the `landrun` and `lean4export` binaries in `PATH`
(`lean4export` must match this project's Lean version, v4.32.2), then:

```
lake build Challenge Solution
lake env path/to/comparator comparator.config.json
```

Comparator then guarantees that the solution proves the same statement as the
challenge, uses no axioms beyond the permitted ones, and is accepted by the Lean
kernel.

---



To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
