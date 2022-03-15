# Abstract model of capability monotonicity in CHERI ISAs

This repository contains a formal model capturing the essential security
property of CHERI instruction-set architectures:  reachable capability
monotonicity.  The model defines a small number of instruction-local properties
that imply the whole-ISA monotonicity property.  This model was used to verify
reachable capability monotonicity for the Morello ISA, a CHERI-enabled
prototype Arm architecture, but the model should also apply to other CHERI
ISAs.

The model, the monotonicity proof, and the instantiation for Morello are
described in the paper (available as PDF [here][morello-formal-paper]):

Verified Security for the Morello Capability-enhanced Prototype Arm Architecture.
Thomas Bauereiss, Brian Campbell, Thomas Sewell, Alasdair Armstrong, Lawrence
Esswood, Ian Stark, Graeme Barnes, Robert N. M. Watson, and Peter Sewell.
In ESOP 2022.

## Structure

The [`model/lem`](model/lem) directory contains the definitions of the
instruction-local properties, written in the [Lem][lem] language.

The [`Properties.thy`](model/isabelle/Properties.thy) file in the
[`model/isabelle`](model/isabelle) directory contains the monotonicity proof
for any ISA satisfying the instruction-local properties, mechanised in the
[Isabelle](https://isabelle.in.tum.de/) interactive theorem prover.

The other files in the [`model/isabelle`](model/isabelle) directory contain
proof infrastructure for verifying the instruction-local properties for a
concrete ISA, and the [`tools`](tools) directory contains a tool for
automatically generating helper lemmas about the bulk of an ISA specification
written in the [Sail][sail] language.

Run `make` in the top-level directory of this repository to build the lemma
generation tool and translate the Lem files of the model into Isabelle
theories.

See the [Morello instantiation][sail-morello-proofs] of the model for an
example of how all these are used.

## Dependencies

* [Isabelle 2020](https://isabelle.in.tum.de/website-Isabelle2020/index.html)
* [Lem][lem]
* [Sail][sail] (last checked with revision `5d18bd95`)

## Licence

The files in this repository are distributed under the BSD 2-clause licence in
[`LICENCE`](LICENCE).

[sail]: https://github.com/rems-project/sail
[lem]: https://github.com/rems-project/lem
[sail-morello-proofs]: https://github.com/CTSRD-CHERI/sail-morello-proofs
[morello-formal-paper]: https://www.cl.cam.ac.uk/~pes20/morello-proofs-esop2022.pdf
