# coho-incidence
This project contains the source code for replicating the numerical evidence showcased in the author's paper "Even-carry polynomials and cohomology of the incidence correspondence in positive characteristic" (see [arxiv:2404.04166](https://arxiv.org/abs/2404.04166)). It contains the following files:

- `print.m2`: Helper code for formatting pictures of symmetric polynomials.
- `S.m2`: Basic methods for symmetric polynomials.
- `h0.m2`: Computes $K(d,e)$ by the method given in Proposition 2.2.
- `prim.m2`: Computes primitive cohomology $K(d,e)^{\mathrm{prim}}$ as described in Section 4.1.
- `tiles.m2`: Explores tiles and produces the tables in Section 4.2.
- `general.m2`: Explores the questions asked in Section 4.3.

Each of these files automatically loads all the preceding ones, except that the last two are independent. So you can launch `M2` in the directory where you downloaded this project and run:
```
load("tiles.m2")
load("general.m2")
```
Some examples of usage follow.

## `h0.m2`
To display a particular $\kappa(d,e)$:
```
graph kappa(2,5)
```
To display all $\kappa(d,e)$ up to a given maximum value of $e$ ($e \leq 30$ by default):
```
allKappa(emax => 10)
```
To compute an individual coefficient of $\kappa(d,e)$ (faster than computing the whole character), or a basis for an individual eigenspace of $K(d,e)$:
```
h0b(2,5,{1,2,3})
H0b(2,5,{1,2,3})
```
**Note:** The values of $n$ and $p$ are coded in `S.m2`. By default, $n = p = 3$. To change these values, modify and reload the file `S.m2`, or use the `updatenp` routine, e.g.
```
n = 4
p = 2
updatenp()
```

## `prim.m2`
To separate $K(d,e)$ into primitive and nonprimitive components:
```
graph kappa(3,4)
graph nonprim(3,4)
graph primChar(3,4)
```
To print a table of primitive characters (like Table 1):
```
primTable(dif => 1, mmax => 10)
```
To print a table of conjectured primitive characters, assuming certain structural hypotheses that are weakened versions of Conjectures 4.7 and 4.9:
```
primGuessTable(dif => 1, mmax => 10)
```
To check that these guesses are correct:
```
primTestAll(dif => 1, mmax => 10)
```
## `tiles.m2`
To find tiles (as in Tables 2, 3, 4):
```
mineTiles(nmin => 3, nmax => 4, pmax => 7, mmax => 15)
```
## `general.m2`
The contents of this file are more more speculative. To guess $\kappa(d,e)$, based on a formula similar to Conjecture 4.10 but missing the unknown terms $P_i(m)$ and trying to infer them instead by truncation:
```
testAll(emax => 15)
testEdge(emax => 30)
```

## Final note
If you use [jEdit](jedit.org) to edit code, please check out my syntax highlighting modes for [MAGMA and Macaulay2](github.com/emo916math/jEdit-modes).

> Written with [StackEdit](https://stackedit.io/).
