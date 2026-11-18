# Reading the proof beside the Lean sources

The paper starts with the least number of Jordan blocks of a nilpotent generator among all counterexamples. Proposition 2.1 turns the dimension of the actual image algebra into a length. This step explains why a pole of a minor detects a counterexample even when the presentation has redundant generators.

| Mathematical step | Source entry |
| --- | --- |
| Ordered monomials span the algebra on the quotient | [BoxWords.lean](../src/BoxWords.lean), `adjoin_box` |
| Smith index, length of the image algebra, strict minor inequality | [IntrinsicDVR.lean](../src/IntrinsicDVR.lean) and [ActorIndex.lean](../src/ActorIndex.lean), `actor_ledger`, `bad_iff_minor` |
| Generic graph and transcendence degree | [GKGraphDimension.lean](../src/GKGraphDimension.lean), `ring_trdeg` |
| Transfer a bad minor to a divisor, then to a genuine finite presentation | [ActualBadTransfer.lean](../src/ActualBadTransfer.lean) and [PoleGlobalWitness.lean](../src/PoleGlobalWitness.lean) |
| Identify the kernel action and constrain both ends | [ActualEnds.lean](../src/ActualEnds.lean), `actual_tail`, and [RealCenters.lean](../src/RealCenters.lean), `actual_center_pairs` |
| Count the two nilpotent pairs and rule out a divisor | [ActualPairParameters.lean](../src/ActualPairParameters.lean), `subregular_pair_parameters`, and [WitnessBudget.lean](../src/WitnessBudget.lean) |
| Three ordinary complex matrices | [FullG3.lean](../src/FullG3.lean), `G3Assembly.complex_three_matrices` |
| Extension of the base field and arbitrary characteristic-zero matrices | [ScalarMatrixActor.lean](../src/ScalarMatrixActor.lean) and [CharZeroMatrices.lean](../src/CharZeroMatrices.lean), `G3Scalar.charZero_three_matrices` |
| Complex theorem expressed with three multiplication equalities | [StatementContract.lean](StatementContract.lean), `all_complex_matrices_contract` |

The geometric proof takes transverse arcs at closed points on the normalization. The formal proof constructs a finite jet at a generic point and transports its endomorphisms to power series. The appendix explains why both constructions preserve the same strict minor inequality. The characteristic-zero condition enters the formal construction of that jet.

## Verification record

Lean **4.36.0-rc2** (commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`) and mathlib `07977d2921637684e9ecdf70fc1927570233637d` are pinned. [Source hashes in compilation order](modules.tsv) cover 136 base modules and the two extension modules.

- Two recorded Linux builds compiled the 136 base modules from empty project object directories on the same machine. They reused pinned upstream objects. All 136 corresponding project objects agreed byte for byte. The complex endpoint object had SHA-256 `c002f1ad745b72e2828932b54b3897679a518ad86e3a3c6102cd4ae0c035dee3`.
- The two characteristic-zero extension modules were compiled into an empty overlay with the verified base objects. Both named matrix theorems report only propositional extensionality, classical choice and quotient soundness.
- The full complex proof export was checked on Linux with nanoda 0.4.17 using [this configuration](nanoda.json). The record retains the [printed statements](recorded-nanoda_type.txt) and a [log excerpt](recorded-nanoda.log) with the machine-local binary path shortened to its basename.
- During preparation of this release, the Rust checker from the pinned Windows toolchain independently read the same 109,568,646 compressed bytes. It checked 68,509 declarations, exited successfully and printed the same two theorem types. [Windows replay record](windows-replay.json)

Proof export SHA-256: `f95f7999e437cc943f0fc2a27828089f8eb800fcb3e720d0923e7a42f19a6319`. The export is a separate release asset to allow a small source checkout.
