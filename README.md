# A Case Study in Dependent Type Theory: Extracting a Certified Program from the Formal Proof of its Specification

## Thesis

LaTeX code for template taken from https://github.com/echo-uib/master-latex-template.

See `.tex-build/main.pdf` for pdf.

## Formalization

### Build Coq files

Proof of main theorem (Theorem 3.2) is located in `coq/src/Main.v`.
Haskell extraction, along with some examples (and minor manual code changes, see thesis 5.1.2), is located in `coq/extr/Main.hs`.
The largest example uses type universe constraints taken from `Main.v`
using `Print Universes`.

```
cd coq
make -f CoqMakefile
```

**Running the above command will also re-extract the file `Main.hs`,
thus removing some changes (done manually for QOL)!**

### Compile & run Haskell example

`coq/extr/Main.hs` can be compiled with Stack for much better efficiency.

```
cd coq/extr/stack-proj
stack run
```
