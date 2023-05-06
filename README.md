# [Title here]

## Build Coq files

```
cd src
make -f CoqMakefile
```

Proof of main theorem (Theorem 3.2) is located in `src/Main.v`.
Haskell extraction, along with some examples (and minor manual code changes), is located in `extr/ex.hs`.
The largest example uses type universe constraints taken from `src/Main.v`
using `Print Universes`.

## Compile & run Haskell example

`extr/ex.hs` can be compiled with Stack for much better efficiency.

```
cd extr/stack-proj
stack run
```
