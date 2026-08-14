# Merris' Conjecture in Dimension Four

The main objective of this repository is to prove the $n=4$ case of Merris'
conjecture on permanents. For a doubly stochastic real matrix
$A\in\mathbb R^{4\times4}$, let $A(r\mid c)$ denote the $3\times3$ matrix
obtained by deleting row $r$ and column $c$, and define

$$
S_c(A)=\sum_{r=1}^4\operatorname{per}(A(r\mid c)).
$$

The target inequality is

$$
\boxed{
4\operatorname{per}(A)\ge
\min_{1\le c\le4}S_c(A).
}
$$

The proof proceeds through a stronger intermediate result: the
Holens--Đoković inequality for the parameter case $(n,i)=(4,4)$,

$$
\boxed{
16\operatorname{per}(A)\ge
\sum_{c=1}^4S_c(A).
}
$$

Indeed, if $c_{\min}$ minimizes $S_c(A)$, then

$$
4S_{c_{\min}}(A)\le\sum_{c=1}^4S_c(A).
$$

Combining these inequalities and dividing by $4$ gives

$$
4\operatorname{per}(A)\ge S_{c_{\min}}(A)
=\min_{1\le c\le4}S_c(A),
$$

which is exactly Merris' conjecture in dimension four. Thus
Holens--Đoković $(4,4)$ is not the final objective of the development; it is
the stronger inequality used to obtain the Merris result.

The general Holens--Đoković conjecture is **false**. Ian M. Wanless disproved
the universal statement in *The Holens--Đoković Conjecture on Permanents
Fails!* (Linear Algebra and its Applications 286 (1999), 273--285,
[DOI: 10.1016/S0024-3795(98)10177-5](https://doi.org/10.1016/S0024-3795(98)10177-5)).
Its failure in general does not prevent individual parameter cases from being
true. This repository establishes the particular case $(4,4)$ and uses it to
derive Merris $n=4$.

Merris introduced the conjecture in *The Permanent of a Doubly Stochastic
Matrix* (American Mathematical Monthly 80 (1973), 791--793,
[DOI: 10.1080/00029890.1973.11993372](https://doi.org/10.1080/00029890.1973.11993372)).
A later paper quotes Merris' general conjecture as

$$
n\operatorname{per}(A)\ge
\min_{1\le i\le n}\sum_{j=1}^n\operatorname{per}(A(j\mid i)),
$$

where $A(j\mid i)$ is obtained by deleting the $j$th row and the $i$th
column. Setting $n=4$ gives exactly the target displayed above; the notation
$c=i$, $r=j$, and $S_c(A)=\sum_r\operatorname{per}(A(r\mid c))$ only renames
the indices. 
That paper also described the conjecture as open for $n\ge4$. This repository
records a Lean-checked proof artifact.

The formal proof first verifies an exact rationally weighted sum-of-squares
(SOS) certificate for a cubic inequality. It then proves that the cubic
inequality is equivalent to the paper-standard Holens--Đoković $(4,4)$
statement and derives the Merris bound. The public Lean theorem `merris_n4`
states the minimum over all four columns directly. The auxiliary theorem
`merris_n4_of_fourth_column_minimal` retains the fixed-column formulation used
in an earlier version of the development.

| Item | Details |
|---|---|
| Result | Lean-checked proof artifact |
| Status | Formalization complete; independent external review not recorded |
| Proof date | 2026-08-13 |
| Institution | East China Normal University |
| Main objective | Merris' conjecture for `n = 4` |
| Proof route | Holens--Đoković `(n,i)=(4,4)` implies Merris `n = 4` |
| Method | Exact rational sum-of-squares certificate |
| Field | Matrix theory; permanents; polynomial optimization |
| Formalization | Lean `4.30.0-rc1` + Mathlib `v4.30.0-rc1` |
| Verification | Exact rational certificate checked with Lean; finite identities use `native_decide` |
| Public theorems | `merris_n4`, `holens_djokovic_4_4`, `holens_djokovic_4_4_cubic` |

## Problem statement

Let

$$
\Omega_4=
\left\{
A=(a_{ij})\in\mathbb R^{4\times4}:
a_{ij}\ge0,\quad
\sum_{j=1}^4a_{ij}=1,\quad
\sum_{i=1}^4a_{ij}=1
\right\}.
$$

The permanent of a matrix $A$ is

$$
\operatorname{per}(A)=
\sum_{\sigma\in S_4}\prod_{i=1}^4a_{i,\sigma(i)}.
$$

For each column $c$, put

$$
S_c(A)=\sum_{r=1}^4\operatorname{per}(A(r\mid c)).
$$

The $n=4$ case of Merris' conjecture asks whether every $A\in\Omega_4$
satisfies

$$
\boxed{
4\operatorname{per}(A)\ge\min_{1\le c\le4}S_c(A).
}
$$

This is the primary statement targeted by the repository.

The corresponding public Lean theorem is:

```lean
theorem merris_n4
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h_nonneg : ∀ i j, 0 ≤ A i j)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    4 * per(A) ≥ min[1≤i≤4] ∑ j : Fin 4, per(A(j ∣ i))
```

### Meaning of the Lean statement

The theorem uses symbolic notation so that its conclusion remains close to
the formula in the paper. Every object, hypothesis, and symbol has the
following meaning:

| Lean expression | Mathematical meaning |
|---|---|
| `A : Matrix (Fin 4) (Fin 4) ℝ` | $A$ is a real $4\times4$ matrix. |
| `h_nonneg : ∀ i j, 0 ≤ A i j` | Every entry $a_{ij}$ is nonnegative. |
| `h_rows : ∀ i, ∑ j, A i j = 1` | Every row of $A$ has sum $1$. |
| `h_columns : ∀ j, ∑ i, A i j = 1` | Every column of $A$ has sum $1$. |
| `per(A)` | $\operatorname{per}(A)$, the permanent of $A$. |
| `A(j ∣ i)` | The $3\times3$ matrix obtained by deleting row $j$ and column $i$ from $A$. |
| `per(A(j ∣ i))` | The permanent of that complementary $3\times3$ submatrix. |
| `∑ j : Fin 4, per(A(j ∣ i))` | For a fixed column $i$, sum the four permanents obtained by deleting each row in turn. |
| `min[1≤i≤4]` | Take the minimum of the preceding sum over the four choices of column $i$. |
| `4 * per(A) ≥ ...` | Four times the permanent of $A$ is at least that minimum. |

The three hypotheses `h_nonneg`, `h_rows`, and `h_columns` together state
that $A$ is doubly stochastic. The symbols `per(A)`, `per(A(j ∣ i))`, and
`min[1≤i≤4]` are notation defined near the start of
[`Theorem.lean`](MerrisN4/Theorem.lean). They expand respectively
to Mathlib's `Matrix.permanent`, `Matrix.submatrix`, and the finite minimum
`Finset.univ.inf'`; they do not hide extra assumptions.

The paper labels rows and columns by $1,2,3,4$, whereas Lean's type `Fin 4`
stores the same four positions internally as `0,1,2,3`. This is only a change
of labels. In particular, `A(j ∣ i)` has exactly the paper's
delete-row/delete-column meaning.

Consequently, this symbolic Lean statement expands definitionally to

$$
4\operatorname{per}(A)\ge
\min_{1\le i\le4}\sum_{j=1}^4\operatorname{per}(A(j\mid i)),
$$

which is the paper's Merris formula specialized to $n=4$.

### Stronger intermediate inequality

For an $n\times n$ matrix, let $\sigma_i(A)$ be the sum of the permanents
of all its $i\times i$ submatrices, with $\sigma_0(A)=1$. The
Holens--Đoković conjecture was originally stated as

$$
\boxed{
i n\,\sigma_i(A)\ge
(n-i+1)^2\sigma_{i-1}(A)
}
\qquad (i=1,\ldots,n).
$$

For $(n,i)=(4,4)$, this becomes

$$
16\sigma_4(A)\ge\sigma_3(A).
$$

Here $\sigma_4(A)=\operatorname{per}(A)$, while every $3\times3$
submatrix is obtained by deleting one row and one column. Thus the standard
paper form used as the stronger intermediate result is

$$
\boxed{
16\operatorname{per}(A)\ge
\sum_{c=1}^4\sum_{r=1}^4
\operatorname{per}(A(r\mid c)).
}
$$

The corresponding public Lean theorem is in
[`Theorem.lean`](MerrisN4/Theorem.lean):

```lean
theorem holens_djokovic_4_4
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h_nonneg : ∀ i j, 0 ≤ A i j)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    16 * per(A) ≥ ∑ i : Fin 4, ∑ j : Fin 4, per(A(j ∣ i))
```

This Lean conclusion is symbol-for-symbol aligned with

$$
16\operatorname{per}(A)\ge
\sum_{i=1}^4\sum_{j=1}^4\operatorname{per}(A(j\mid i)).
$$

Here `per(A)` means $\operatorname{per}(A)$, and `per(A(j ∣ i))` means the
permanent after deleting row $j$ and column $i$. For each fixed deleted column
$i$, the inner sum runs over the four deleted rows $j$; the outer sum then
runs over all four deleted columns. The right-hand side contains all sixteen
complementary $3\times3$ permanents and is exactly $\sigma_3(A)$. As in the
Merris theorem, `Fin 4` uses the internal labels `0,1,2,3` for the paper's
$1,2,3,4$.

## Formalized results

Lean checks the two main results in the proof chain.

1. **Merris `n = 4`:** for every $4\times4$ doubly stochastic real matrix,

   $$
   4\operatorname{per}(A)\ge\min_{1\le c\le4}S_c(A).
   $$
2. **Holens--Đoković `(4,4)`:** the stronger standard subpermanent
   inequality

   $$
   16\operatorname{per}(A)\ge\sum_{c=1}^4S_c(A)
   $$

   holds for every $4\times4$ doubly stochastic real matrix.

The auxiliary theorem `merris_n4_of_fourth_column_minimal` states the same
argument on the chamber $S_4(A)\le S_c(A)$ for $c=1,2,3$. It is retained for
convenience, while `merris_n4` is the complete standard statement.

## Method

### 1. Nine-variable parametrization

Take the upper-left $3\times3$ block of $A$ as nine free variables:

$$
u=(u_{11},u_{12},u_{13},u_{21},u_{22},u_{23},u_{31},u_{32},u_{33}).
$$

The remaining seven entries are uniquely determined by the row-sum and
column-sum equations:

$$
a_{i4}=1-\sum_{j=1}^3u_{ij},\qquad
a_{4j}=1-\sum_{i=1}^3u_{ij},\qquad
a_{44}=\sum_{i,j=1}^3u_{ij}-2.
$$

This converts the original problem, without relaxation, into the nonnegativity
of the nine-variable polynomial corresponding to the equivalent cubic form

$$
\Phi(u)=24\operatorname{per}(A(u))-2-
\sum_{i,j=1}^4a_{ij}(u)^3
$$

under the sixteen linear constraints $a_{ij}(u)\ge0$.

### 2. Symmetrized exact SOS certificate

The target polynomial is invariant under row permutations, column
permutations, and transposition. The code explicitly stores the
$24\cdot24\cdot2=1152$ transformations as cell mappings and uses four classes
of nonnegative multipliers:

$$
m_0=a_{41}a_{42}a_{43}a_{44},\qquad
m_1=a_{44},\qquad
m_2=a_{44}a_{43},\qquad
m_3=a_{44}a_{33}.
$$

The certificate has the form

$$
\boxed{
\Phi(u)=
\sum_{r=0}^3\sum_{\tau}\sum_k
\lambda_{r,k}\,
m_r(\tau A(u))\,
q_{r,k}(\tau A(u))^2,
}
$$

Every weight $\lambda_{r,k}$ is a nonnegative rational number, and every
$q_{r,k}$ is a polynomial with rational coefficients. For
$A\in\Omega_4$, the multipliers, weights, and squared terms are all
nonnegative, so the right-hand side is nonnegative.

| Block | Representative multiplier | Weighted squares | Slices |
|---|---|---:|---:|
| `Block0` | $a_{41}a_{42}a_{43}a_{44}$ | 9 | 8 |
| `Block1` | $a_{44}$ | 24 | 16 |
| `Block2` | $a_{44}a_{43}$ | 42 | 24 |
| `Block3` | $a_{44}a_{33}$ | 34 | 24 |

The complete certificate is divided into $8+16+24+24=72$ slices for parallel
compilation. Slicing is only an engineering partition and does not alter the
mathematical certificate.

### 3. From the cubic certificate to the paper statement

Write

$$
\sigma_3(A)=
\sum_{c=1}^4\sum_{r=1}^4
\operatorname{per}(A(r\mid c)).
$$

The formalization proves the following identity for every $4\times4$ doubly
stochastic matrix:

$$
3\sum_{c=1}^4S_c(A)=4+2\sum_{i,j=1}^4a_{ij}^3.
$$

Consequently,

$$
16\operatorname{per}(A)\ge\sigma_3(A)
\quad\Longleftrightarrow\quad
24\operatorname{per}(A)-2-
\sum_{i,j=1}^4a_{ij}^3\ge0.
$$

The theorem `holens_djokovic_4_4_cubic` records the right-hand inequality
proved by the SOS certificate. The public theorem `holens_djokovic_4_4` then
uses the displayed identity to derive the paper-standard statement on the
left.

### 4. Deriving the main Merris result

For each column $c$, define its complementary permanent sum by

$$
S_c(A)=\sum_{r=1}^4\operatorname{per}(A(r\mid c)).
$$

Thus $S_c(A)$ is the sum of the four $3\times3$ permanents obtained by
deleting column $c$ and, in turn, one of the four rows. The phrase "minimum
column" below refers to the column minimizing $S_c(A)$; it does not refer to
the ordinary column sum, since every ordinary column sum of a doubly
stochastic matrix is already equal to $1$.

The main target, Merris' conjectured inequality in dimension four, is

$$
\boxed{
4\operatorname{per}(A)\ge \min_{1\le c\le4}S_c(A).
}
$$

Equivalently, choose a column $c_{\min}$ satisfying
$S_{c_{\min}}(A)=\min_c S_c(A)$ and prove

$$
4\operatorname{per}(A)\ge S_{c_{\min}}(A).
$$

This follows directly from the stronger Holens--Đoković `(4,4)` result.
Indeed,

$$
\sigma_3(A)=\sum_{c=1}^4S_c(A),
$$

and minimality gives

$$
4S_{c_{\min}}(A)\le\sum_{c=1}^4S_c(A)=\sigma_3(A).
$$

Combining this with
$16\operatorname{per}(A)\ge\sigma_3(A)$ and dividing by $4$ gives the
Merris bound.

The auxiliary Lean theorem `merris_n4_of_fourth_column_minimal` fixes
$c_{\min}=4$ (represented by index `3` in Lean's zero-based `Fin 4`). Its
three extra hypotheses state

$$
S_4(A)\le S_1(A),\qquad
S_4(A)\le S_2(A),\qquad
S_4(A)\le S_3(A),
$$

and its conclusion is $4\operatorname{per}(A)\ge S_4(A)$. The main theorem
`merris_n4` no longer requires this choice: it uses `Finset.univ.inf'` to take
the minimum of $S_c(A)$ over all four columns directly.

## Certificate generation

Certificate discovery and certificate verification are separate stages:

1. Search for candidate Gram data by semidefinite programming on the
   nine-variable model.
2. Use known equality cases, including the uniform matrix, to impose
   vanishing conditions and reduce the Gram-block dimensions.
3. Recover exact rational data from the numerical candidate and factor it into
   terms of the form $\lambda_{r,k}q_{r,k}^2$.
4. Export the weights, polynomials, mappings, and target coefficients as Lean
   data.
5. Lean does not trust the search process: it re-expands the exported rational
   data and verifies the complete identity.

Rechecking this repository does not require the original floating-point Gram
matrices, Julia, or Mosek. Those belong to certificate discovery and are not
dependencies of the final verification.

## Verification

The Lean verification chain is as follows:

1. [`SparsePolyCheck.lean`](MerrisN4/SparsePolyCheck.lean) defines sparse
   polynomials, normalization, and real evaluation semantics, and proves that
   addition, multiplication, squaring, and normalization preserve evaluation.
2. [`FastPolyForSOS.lean`](MerrisN4/FastPolyForSOS.lean) uses a
   `TreeMap` implementation to accelerate sparse polynomial operations; its
   public semantic lemmas remain connected to the basic definitions.
3. [`Common.lean`](MerrisN4/Common.lean) defines substitution,
   symmetry orbits, weighted sums of squares, and nonnegative multipliers, and
   proves that every orbit certificate evaluates to a nonnegative number.
4. Each `Block*/Slice*.lean` checks weight nonnegativity and verifies the exact
   identity `fastNormalize certificate = target`.
5. [`Certificate.lean`](MerrisN4/Certificate.lean) checks that the
   sum of the four blocks equals the target polynomial in
   [`TargetData.lean`](MerrisN4/TargetData.lean), and also checks
   that the compact expression `24 * permanent - 2 - cubeSum` normalizes to
   the same target.
6. [`Theorem.lean`](MerrisN4/Theorem.lean) connects evaluation of the
   nine-variable polynomial back to Mathlib's `Matrix.permanent`, proves the
   cubic/subpermanent identity, and derives the paper-standard statement for
   an arbitrary $A\in\Omega_4$.

All certificate coefficients are exact rational numbers. Verification does not
rely on floating-point tolerances, random sampling, or a finite collection of
test points. The source contains no `sorry`, `admit`, or project-defined
`axiom`.

Large finite equalities use `native_decide`. The trusted base for these steps
therefore includes Lean's native code generator and runtime in addition to the
Lean kernel and Mathlib. The repository does not record an independent expert
review, nor does it formalize historical or novelty claims; it provides a
reproducibly compilable formal proof artifact.

## Source

```text
MerrisN4.lean                 Top-level import
MerrisN4/
  Theorem.lean                            Public standard, cubic, and Merris theorems
  Certificate.lean                        Connects four blocks to the target
  Common.lean                             Parametrization and SOS lemmas
  SparsePolyCheck.lean                    Sparse polynomial semantics
  FastPolyForSOS.lean                     Fast sparse polynomial operations
  MappingsData.lean                       1152 explicit cell mappings
  TargetData.lean                         Expanded target polynomial
  Block0Data.lean ... Block3Data.lean     Four exact rational certificates
  Block0/ ... Block3/                     72 independently checked slices
  build_parallel.sh                       Parallel build script
lakefile.toml
lake-manifest.json
lean-toolchain
```

## Reproduce

After installing [elan](https://github.com/leanprover/elan), run the following
commands from the project root:

```bash
lake update
lake exe cache get
MERRIS_N4_LEAN_JOBS=12 bash MerrisN4/build_parallel.sh
```

`MERRIS_N4_LEAN_JOBS` controls the number of slices compiled concurrently and should
be adjusted for the available CPU and memory. The script first builds the
shared data, then checks the 72 slices in parallel, and finally combines the
four blocks and compiles the public theorems.

The final theorem file can also be checked directly:

```bash
lake env lean MerrisN4/Theorem.lean
```

For an incremental build, run:

```bash
lake build
```

Generated `.olean` files, the Mathlib cache, and build logs are stored under
`.lake/` and should not be committed.
