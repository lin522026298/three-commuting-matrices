# A Solution to the Gerstenhaber Problem for Three Commuting Matrices

Yan-cheng Lin · Paper v1.1 · [Read the paper](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Zenodo DOI](https://doi.org/10.5281/zenodo.24346423)

If three endomorphisms of an *n*-dimensional space commute pairwise, their unital algebra has dimension at most *n*. The geometric proof works over every field. It shows how a violation on one finite-length module would force a divisor of violations, then bounds the dimension of its image using two actions on the same module.

The compared theorem is `Gerstenhaber.finrank_adjoin_triple_le`, as stated in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/d8d031d4998c78575159ccab9a7a9e95ce043883/FormalConjectures/Other/GerstenhaberThreeMatrices.lean#L55-L66).
Its quantifiers include fields of positive characteristic and matrices of size
zero. The paper's Section 6 applications are separate results.

In positive characteristic the formal argument first passes to an
algebraic closure. Over this perfect field, the finite-normalization
argument treats the inseparable part of the function-field extension
using Frobenius. At the chosen divisor the residue field is essentially
of finite type over the base, so formal smoothness provides the coefficient
section needed for the finite jet. Extension of scalars preserves the
dimension of the generated algebra, giving the result over the original field.

## Reproduce the all-fields proof

[Challenge.lean](Challenge.lean) states the theorem using only mathlib.
[Solution.lean](Solution.lean) proves that statement using the three-matrix
theorem in [AllFieldMatrices.lean](src/AllFieldMatrices.lean). Use the pinned
Lean and mathlib revisions in this repository. From the root, on Linux with
the Comparator sandbox and bundled checkers available, run:

```sh
lake exe cache get
lake build Challenge Solution
lake comparator --config comparator.json
```

The source metadata, AI disclosure and relationship to the written
proof appear in [formalization.yaml](formalization.yaml).

## Check the complex theorem from the proof terms

The [v1.1 release](https://github.com/lin522026298/three-commuting-matrices/releases/tag/v1.1) contains the historical proof export `complex_contract_proof.jsonl.gz`. Its replay and CI records concern that version and its complex or characteristic-zero declarations. To reproduce the complex proof check, download the export and v1.1 source package. The pinned Lean distribution includes the Rust checker `nanoda_bin`. With that executable on PATH, run

```sh
python3 scripts/check_export.py /path/to/complex_contract_proof.jsonl.gz
```

Alternatively pass `--checker /path/to/nanoda_bin`. On Windows use the path to `nanoda_bin.exe`. This route needs the checker, Python and the compressed proof. It reads no mathlib cache. The script validates the SHA-256, checks the terms under a three-axiom allowlist, and compares the two printed theorem types with the reference output. [Verification record](verification/guide.md#verification-record)

## Citation and licenses

The author and version are recorded in [CITATION.cff](CITATION.cff). The original proof sources and checking scripts carry the [MIT license](LICENSE). The paper and its LaTeX source carry [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Upstream contributions represented in the serialized proof keep their original licenses, included in [LICENSES](LICENSES).
