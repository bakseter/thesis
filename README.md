# A Case Study in Dependent Type Theory: Extracting a Certified Program from the Formal Proof of its Specification

## Build Coq files

```
cd coq
make -f CoqMakefile
```

Proof of main theorem (Theorem 3.2) is located in `coq/src/Main.v`.
Haskell extraction, along with some examples (and minor manual code changes, see thesis 5.1.2), is located in `coq/extr/Main.hs`.
The largest example uses type universe constraints taken from `src/Main.v`
using `Print Universes`.

## Compile & run Haskell example

`coq/extr/Main.hs` can be compiled with Stack for much better efficiency.

```
cd coq/extr/stack-proj
stack run
```
