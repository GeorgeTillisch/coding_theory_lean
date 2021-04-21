# Some Coding Theory In Lean

This project contains some formalized coding theory, written in [Lean 3](https://leanprover.github.io/). See the accompanying report for more details.

## Setup & Installation

The best way to read this code is using a local installation of Lean.
See the [Lean Community Guide](https://leanprover-community.github.io/get_started.html) for instructions. 

Once installed, run 
```
leanproject build
leanproject get-mathlib-cache
``` 
in this directory to setup the project.

## Project Overview

- `binary.lean`
    - Contains fundamental definitions: bits, binary words, binary word matrices.
    - Namespaces: `B` for bits, `BW` for binary words, `BWM` for binary word matrices.
- `hamming.lean`
    - Contains definitions of Hamming distance and weight and proofs of basic properties.
    - Namespace: `hamming` so that one can write `hamming.distance` or `hamming.weight`.
    - Also includes notation for these functions: `d(x,y)` and `wt(x)`.
- `binary_codes.lean`
    - Contains the definition of a binary code and the main proofs of the project, see comments in file for more details.
    - All contained in namespace `binary_code`.
- `binary_linear_codes.lean`
    - Defines an extension of binary codes, linear binary codes.
    - Also contains an example linear code, the Hamming(7,4) code, and contains proofs of some basic properties of this code.
- `syndrome_decoding.lean`
    - Contains a formalization of the Hamming(7,4) code and a proof that syndrome decoding is a 1-error correcting decoding procedure for this code.
- `qary_codes_example.lean`
    - Contains examples of the distance and weight functions defined for q-ary words (vectors) and some sample proofs.
- `hamcode_widget.lean`
    - Contains an interactive widget showing the encoding/decoding procedure for the Hamming(7,4) code.
    - See the [mathlib documentation](https://leanprover-community.github.io/mathlib_docs/init/meta/widget/basic.html) on widgets for more information.