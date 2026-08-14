import Mathlib
import MerrisN4.Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4

open scoped BigOperators
open SparsePolyCheck FastPolyForSOS
open Certificate

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

def complementaryMinorPermanent
    (A : Matrix4) (row column : Fin 4) : ℝ :=
  Matrix.permanent (A.submatrix row.succAbove column.succAbove)

-- Paper notation for the permanent of a complementary minor.
syntax:max "per(" term:max "(" term:max "∣" term:max ")" ")" : term
macro_rules
  | `(per( $A:term ( $row:term ∣ $column:term ) )) =>
      `(complementaryMinorPermanent $A $row $column)
-- Paper notation for the permanent of a matrix.
syntax:max "per(" term:max ")" : term
macro_rules
  | `(per( $A:term )) => `(Matrix.permanent $A)
-- The minimum over the four elements of `Fin 4`, displayed with paper-style bounds.
syntax:60 "min[1≤" ident "≤4] " term:60 : term
macro_rules
  | `(min[1≤$column:ident≤4] $value:term) =>
      `(Finset.univ.inf' Finset.univ_nonempty
        (fun $column : Fin 4 => $value))

def pointOfMatrix (A : Matrix4) (index : Fin 9) : ℝ :=
  match index.val with
  | 0 => A 0 0
  | 1 => A 0 1
  | 2 => A 0 2
  | 3 => A 1 0
  | 4 => A 1 1
  | 5 => A 1 2
  | 6 => A 2 0
  | 7 => A 2 1
  | _ => A 2 2

def entryValue (x : Fin 9 → ℝ) (index : Nat) : ℝ :=
  eval x (entry index)

def matrixOfPoint (x : Fin 9 → ℝ) : Matrix4 :=
  ![![entryValue x 0, entryValue x 1, entryValue x 2, entryValue x 3],
    ![entryValue x 4, entryValue x 5, entryValue x 6, entryValue x 7],
    ![entryValue x 8, entryValue x 9, entryValue x 10, entryValue x 11],
    ![entryValue x 12, entryValue x 13, entryValue x 14, entryValue x 15]]

private theorem matrixOfPoint_pointOfMatrix
    (A : Matrix4)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    matrixOfPoint (pointOfMatrix A) = A := by
  have hr0 := h_rows (0 : Fin 4)
  have hr1 := h_rows (1 : Fin 4)
  have hr2 := h_rows (2 : Fin 4)
  have hr3 := h_rows (3 : Fin 4)
  have hc0 := h_columns (0 : Fin 4)
  have hc1 := h_columns (1 : Fin 4)
  have hc2 := h_columns (2 : Fin 4)
  simp only [Fin.sum_univ_four] at hr0 hr1 hr2 hr3 hc0 hc1 hc2
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [matrixOfPoint, entryValue, entry, entryPolys, pointOfMatrix,
      fastSum] <;> linarith

private theorem entriesNonnegative_pointOfMatrix
    (A : Matrix4)
    (h_nonneg : ∀ i j, 0 ≤ A i j)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    EntriesNonnegative (pointOfMatrix A) := by
  let x := pointOfMatrix A
  have hmatrix : matrixOfPoint x = A :=
    matrixOfPoint_pointOfMatrix A h_rows h_columns
  have hmatrixNonnegative : ∀ i j, 0 ≤ matrixOfPoint x i j := by
    intro i j
    rw [hmatrix]
    exact h_nonneg i j
  intro index
  change 0 ≤ entryValue x index
  by_cases hindex : index < 16
  · interval_cases index <;>
      first
      | simpa [matrixOfPoint] using hmatrixNonnegative 0 0
      | simpa [matrixOfPoint] using hmatrixNonnegative 0 1
      | simpa [matrixOfPoint] using hmatrixNonnegative 0 2
      | simpa [matrixOfPoint] using hmatrixNonnegative 0 3
      | simpa [matrixOfPoint] using hmatrixNonnegative 1 0
      | simpa [matrixOfPoint] using hmatrixNonnegative 1 1
      | simpa [matrixOfPoint] using hmatrixNonnegative 1 2
      | simpa [matrixOfPoint] using hmatrixNonnegative 1 3
      | simpa [matrixOfPoint] using hmatrixNonnegative 2 0
      | simpa [matrixOfPoint] using hmatrixNonnegative 2 1
      | simpa [matrixOfPoint] using hmatrixNonnegative 2 2
      | simpa [matrixOfPoint] using hmatrixNonnegative 2 3
      | simpa [matrixOfPoint] using hmatrixNonnegative 3 0
      | simpa [matrixOfPoint] using hmatrixNonnegative 3 1
      | simpa [matrixOfPoint] using hmatrixNonnegative 3 2
      | simpa [matrixOfPoint] using hmatrixNonnegative 3 3
  · have hlength : entryPolys.length ≤ index := by
      simpa [entryPolys] using Nat.le_of_not_gt hindex
    have hout : entryPolys[index]? = none := by
      exact List.getElem?_eq_none hlength
    simp [entryValue, entry, List.getD_eq_getElem?_getD, hout]

private theorem matrixOfPoint_apply (x : Fin 9 → ℝ)
    (row column : Fin 4) :
    matrixOfPoint x row column =
      entryValue x (4 * row.val + column.val) := by
  fin_cases row <;> fin_cases column <;> rfl

private theorem eval_permanentPoly (x : Fin 9 → ℝ) :
    eval x permanentPoly = Matrix.permanent (matrixOfPoint x) := by
  symm
  rw [Matrix.permanent]
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm
    (fun permutation : Equiv.Perm (Fin 4) =>
      ∏ row, matrixOfPoint x (permutation row) row)]
  rw [Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  simp_rw [matrixOfPoint_apply]
  norm_num [Equiv.swap_apply_def, Fin.ext_iff, permanentPoly, entryValue,
    entry, fastSum, fastProduct]
  ring_nf

private theorem eval_cubeSumPoly (x : Fin 9 → ℝ) :
    eval x cubeSumPoly =
      ∑ row : Fin 4, ∑ column : Fin 4, (matrixOfPoint x row column) ^ 3 := by
  simp_rw [matrixOfPoint_apply]
  simp only [Fin.sum_univ_succ]
  norm_num [cubeSumPoly, entryValue, entry, entryPolys,
    fastSum]
  ring_nf

private theorem eval_compactTarget (x : Fin 9 → ℝ) :
    eval x compactTarget =
      24 * Matrix.permanent (matrixOfPoint x) - 2 -
        ∑ row : Fin 4, ∑ column : Fin 4,
          (matrixOfPoint x row column) ^ 3 := by
  simp [compactTarget, eval_permanentPoly, eval_cubeSumPoly]

/-- An equivalent cubic form of Holens--Djokovic `(4,4)`, used by the SOS certificate. -/
theorem holens_djokovic_4_4_cubic
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h_nonneg : ∀ i j, 0 ≤ A i j)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    0 ≤ 24 * Matrix.permanent A - 2 -
      ∑ i, ∑ j, (A i j) ^ 3 := by
  let x := pointOfMatrix A
  have hentries : EntriesNonnegative x :=
    entriesNonnegative_pointOfMatrix A h_nonneg h_rows h_columns
  have hcompact : 0 ≤ eval x compactTarget :=
    Certificate.eval_compactTarget_nonneg x hentries
  rw [eval_compactTarget] at hcompact
  have hmatrix : matrixOfPoint x = A :=
    matrixOfPoint_pointOfMatrix A h_rows h_columns
  simpa only [hmatrix] using hcompact

private theorem permanent_fin_three
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.permanent M =
      M 0 0 * M 1 1 * M 2 2 +
      M 0 0 * M 2 1 * M 1 2 +
      M 1 0 * M 0 1 * M 2 2 +
      M 1 0 * M 2 1 * M 0 2 +
      M 2 0 * M 0 1 * M 1 2 +
      M 2 0 * M 1 1 * M 0 2 := by
  rw [Matrix.permanent]
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm
    (fun permutation : Equiv.Perm (Fin 3) =>
      ∏ column, M (permutation column) column)]
  rw [Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  norm_num [Equiv.swap_apply_def, Fin.ext_iff]
  ring

private theorem sigma_three_identity
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    3 * (∑ column : Fin 4, ∑ row : Fin 4,
      Matrix.permanent
        (A.submatrix row.succAbove column.succAbove)) =
      4 + 2 * ∑ i : Fin 4, ∑ j : Fin 4, (A i j) ^ 3 := by
  have succAbove0 : (0 : Fin 4).succAbove = ![1, 2, 3] := by
    funext i
    fin_cases i <;> decide
  have succAbove1 : (1 : Fin 4).succAbove = ![0, 2, 3] := by
    funext i
    fin_cases i <;> decide
  have succAbove2 : (2 : Fin 4).succAbove = ![0, 1, 3] := by
    funext i
    fin_cases i <;> decide
  have succAbove3 : (3 : Fin 4).succAbove = ![0, 1, 2] := by
    funext i
    fin_cases i <;> decide
  have hr0 := h_rows (0 : Fin 4)
  have hr1 := h_rows (1 : Fin 4)
  have hr2 := h_rows (2 : Fin 4)
  have hr3 := h_rows (3 : Fin 4)
  have hc0 := h_columns (0 : Fin 4)
  have hc1 := h_columns (1 : Fin 4)
  have hc2 := h_columns (2 : Fin 4)
  simp only [Fin.sum_univ_four] at hr0 hr1 hr2 hr3 hc0 hc1 hc2
  have ha03 : A 0 3 = 1 - A 0 0 - A 0 1 - A 0 2 := by
    linarith
  have ha13 : A 1 3 = 1 - A 1 0 - A 1 1 - A 1 2 := by
    linarith
  have ha23 : A 2 3 = 1 - A 2 0 - A 2 1 - A 2 2 := by
    linarith
  have ha30 : A 3 0 = 1 - A 0 0 - A 1 0 - A 2 0 := by
    linarith
  have ha31 : A 3 1 = 1 - A 0 1 - A 1 1 - A 2 1 := by
    linarith
  have ha32 : A 3 2 = 1 - A 0 2 - A 1 2 - A 2 2 := by
    linarith
  have ha33 : A 3 3 =
      A 0 0 + A 0 1 + A 0 2 +
      A 1 0 + A 1 1 + A 1 2 +
      A 2 0 + A 2 1 + A 2 2 - 2 := by
    linarith
  simp only [Fin.sum_univ_four, permanent_fin_three,
    Matrix.submatrix_apply, succAbove0, succAbove1, succAbove2, succAbove3]
  simp
  rw [ha03, ha13, ha23, ha30, ha31, ha32, ha33]
  ring

/--
The Holens--Djokovic inequality in the parameter case `(n, k) = (4, 4)`,
written in the paper-standard form

`16 * per(A) ≥ ∑ i : Fin 4, ∑ j : Fin 4, per(A(j ∣ i))`.

Here `A` is a real `4 x 4` doubly stochastic matrix, as expressed by
`h_nonneg`, `h_rows`, and `h_columns`. The symbol `per(A)` is the permanent of
`A`. For a fixed column `i`, `per(A(j ∣ i))` is the permanent of the `3 x 3`
matrix obtained by deleting row `j` and column `i`. The inner sum ranges over
all four deleted rows, and the outer sum ranges over all four deleted columns.
The right-hand side is therefore the sum of the permanents of all sixteen
`3 x 3` submatrices of `A`, namely `sigma_3(A)`.

The paper uses indices `1, 2, 3, 4`; Lean represents the same four positions
by `Fin 4`, internally numbered `0, 1, 2, 3`.
-/
theorem holens_djokovic_4_4
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h_nonneg : ∀ i j, 0 ≤ A i j)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    16 * per(A) ≥ ∑ i : Fin 4, ∑ j : Fin 4, per(A(j ∣ i)) := by
  have h_cubic :=
    holens_djokovic_4_4_cubic A h_nonneg h_rows h_columns
  have h_sigma := sigma_three_identity A h_rows h_columns
  nlinarith

/-- The sum of the four complementary `3 x 3` permanents for a fixed column. -/
def complementaryPermanentSum
    (A : Matrix (Fin 4) (Fin 4) ℝ) (column : Fin 4) : ℝ :=
  ∑ row : Fin 4, Matrix.permanent
    (A.submatrix row.succAbove column.succAbove)

/--
Merris' inequality at `n = 4`, on the chamber where the fourth column
minimizes the sum of the four complementary `3 x 3` permanents.
-/
theorem merris_n4_of_fourth_column_minimal
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h_nonneg : ∀ i j, 0 ≤ A i j)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1)
    (h_min_column_1 :
      0 ≤ (∑ row : Fin 4, Matrix.permanent
          (A.submatrix row.succAbove (0 : Fin 4).succAbove)) -
        ∑ row : Fin 4, Matrix.permanent
          (A.submatrix row.succAbove (3 : Fin 4).succAbove))
    (h_min_column_2 :
      0 ≤ (∑ row : Fin 4, Matrix.permanent
          (A.submatrix row.succAbove (1 : Fin 4).succAbove)) -
        ∑ row : Fin 4, Matrix.permanent
          (A.submatrix row.succAbove (3 : Fin 4).succAbove))
    (h_min_column_3 :
      0 ≤ (∑ row : Fin 4, Matrix.permanent
          (A.submatrix row.succAbove (2 : Fin 4).succAbove)) -
        ∑ row : Fin 4, Matrix.permanent
          (A.submatrix row.succAbove (3 : Fin 4).succAbove)) :
    0 ≤ 4 * Matrix.permanent A -
      ∑ row : Fin 4, Matrix.permanent
        (A.submatrix row.succAbove (3 : Fin 4).succAbove) := by
  have h_hd := holens_djokovic_4_4 A h_nonneg h_rows h_columns
  let S : Fin 4 → ℝ := fun column =>
    ∑ row : Fin 4, Matrix.permanent
      (A.submatrix row.succAbove column.succAbove)
  change 0 ≤ S 0 - S 3 at h_min_column_1
  change 0 ≤ S 1 - S 3 at h_min_column_2
  change 0 ≤ S 2 - S 3 at h_min_column_3
  change 0 ≤ 4 * Matrix.permanent A - S 3
  change 16 * Matrix.permanent A ≥ ∑ column : Fin 4, S column at h_hd
  have h_min_sum : 4 * S 3 ≤ ∑ column : Fin 4, S column := by
    rw [Fin.sum_univ_four]
    linarith
  linarith

/--
Merris' conjectured inequality in dimension four, in its standard paper form:

`4 * per(A) ≥ min[1≤i≤4] ∑ j : Fin 4, per(A(j ∣ i))`.

Meaning of the objects and symbols:

* `A : Matrix (Fin 4) (Fin 4) ℝ` is a real `4 x 4` matrix.
* `h_nonneg` says that every entry `A i j` is nonnegative.
* `h_rows` and `h_columns` say that every row sum and every column sum is
  `1`; together with `h_nonneg`, these hypotheses say that `A` is doubly
  stochastic.
* `per(A)` is `Matrix.permanent A`, the permanent of `A`.
* `per(A(j ∣ i))` is the permanent of the `3 x 3` matrix obtained by deleting
  row `j` and column `i` from `A`.
* `∑ j : Fin 4, per(A(j ∣ i))` sums the four complementary permanents obtained
  by fixing column `i` and deleting each of the four rows in turn.
* `min[1≤i≤4]` is paper-style notation for `Finset.univ.inf'` on `Fin 4`; it
  takes the minimum of the preceding sum over all four columns.
* `≥` asserts that four times the permanent of `A` is at least this minimum.

The paper labels rows and columns by `1, 2, 3, 4`, while `Fin 4` represents
the same four positions internally by `0, 1, 2, 3`. The notation changes only
the presentation: it expands definitionally to Mathlib's permanent,
submatrix, finite sum, and finite infimum operations.
-/
theorem merris_n4
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h_nonneg : ∀ i j, 0 ≤ A i j)
    (h_rows : ∀ i, ∑ j, A i j = 1)
    (h_columns : ∀ j, ∑ i, A i j = 1) :
    4 * per(A) ≥ min[1≤i≤4] ∑ j : Fin 4, per(A(j ∣ i)) := by
  have h_hd := holens_djokovic_4_4 A h_nonneg h_rows h_columns
  let S : Fin 4 → ℝ := fun column =>
    ∑ row : Fin 4, Matrix.permanent
      (A.submatrix row.succAbove column.succAbove)
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty S
  change 16 * Matrix.permanent A ≥ ∑ column : Fin 4, S column at h_hd
  change 4 * Matrix.permanent A ≥ m
  have h_min (column : Fin 4) : m ≤ S column := by
    exact Finset.inf'_le (f := S) (by simp)
  have h_min_sum : 4 * m ≤ ∑ column : Fin 4, S column := by
    rw [Fin.sum_univ_four]
    linarith [h_min 0, h_min 1, h_min 2, h_min 3]
  linarith

end MerrisN4
