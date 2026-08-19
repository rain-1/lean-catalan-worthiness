This project was edited by [Aristotle](https://aristotle.harmonic.fun).

## Metadata

See [formalization.yaml](./formalization.yaml) for provenance, scope, axioms, and
review status, following the
[mathlib-initiative/formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml)
standard. Validate it with:

```
check-jsonschema --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json formalization.yaml
```

## Verifying the main result with comparator

The main theorem (`Catalan.catalan_worthiness_gt_857914`, RequestProject/Final.lean)
can be checked with [leanprover/comparator](https://github.com/leanprover/comparator):

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