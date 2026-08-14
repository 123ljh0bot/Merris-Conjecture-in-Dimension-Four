import Mathlib

namespace SparsePolyCheck

abbrev Exp (n : Nat) := Fin n → Nat

structure Term (n : Nat) where
  exp : Exp n
  coeff : ℚ
  deriving DecidableEq

abbrev Poly (n : Nat) := List (Term n)

def expKey {n : Nat} (e : Exp n) : Nat :=
  (List.ofFn e).foldl (fun code exponent => code * 5 + exponent) 0

def expAdd {n : Nat} (a b : Exp n) : Exp n := fun i => a i + b i

def insertTerm {n : Nat} (term : Term n) : Poly n → Poly n
  | [] => [term]
  | head :: tail =>
      if expKey term.exp < expKey head.exp then
        term :: head :: tail
      else if term.exp = head.exp then
        { exp := head.exp, coeff := term.coeff + head.coeff } :: tail
      else
        head :: insertTerm term tail

def clean {n : Nat} : Poly n → Poly n
  | [] => []
  | term :: tail => if term.coeff = 0 then clean tail else term :: clean tail

def termLE {n : Nat} (left right : Term n) : Bool :=
  decide (expKey left.exp ≤ expKey right.exp)

def normalize {n : Nat} (poly : Poly n) : Poly n :=
  clean ((poly.mergeSort termLE).foldr insertTerm [])

def mergeSorted {n : Nat} : Poly n → Poly n → Poly n
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
      if expKey leftHead.exp < expKey rightHead.exp then
        leftHead :: mergeSorted leftTail (rightHead :: rightTail)
      else if expKey rightHead.exp < expKey leftHead.exp then
        rightHead :: mergeSorted (leftHead :: leftTail) rightTail
      else if leftHead.exp = rightHead.exp then
        let coefficient := leftHead.coeff + rightHead.coeff
        if coefficient = 0 then
          mergeSorted leftTail rightTail
        else
          { exp := leftHead.exp, coeff := coefficient } :: mergeSorted leftTail rightTail
      else
        leftHead :: mergeSorted leftTail (rightHead :: rightTail)

def mergeMany {n : Nat} : List (Poly n) → Poly n
  | [] => []
  | poly :: polys => mergeSorted poly (mergeMany polys)

def add {n : Nat} (left right : Poly n) : Poly n := left ++ right

def mulTerm {n : Nat} (left right : Term n) : Term n :=
  { exp := expAdd left.exp right.exp, coeff := left.coeff * right.coeff }

def mulRaw {n : Nat} (left right : Poly n) : Poly n :=
  left.flatMap fun leftTerm => right.map (mulTerm leftTerm)

def mul {n : Nat} (left right : Poly n) : Poly n := mulRaw left right

def zeroExp (n : Nat) : Exp n := fun _ => 0

def const {n : Nat} (coefficient : ℚ) : Poly n :=
  if coefficient = 0 then [] else [{ exp := zeroExp n, coeff := coefficient }]

def var {n : Nat} (index : Fin n) : Poly n :=
  [{ exp := fun current => if current = index then 1 else 0, coeff := 1 }]

def monoPoly {n : Nat} (exponent : Exp n) : Poly n :=
  [{ exp := exponent, coeff := 1 }]

def scale {n : Nat} (coefficient : ℚ) (poly : Poly n) : Poly n :=
  poly.map fun term => { term with coeff := coefficient * term.coeff }

def neg {n : Nat} (poly : Poly n) : Poly n := scale (-1) poly

def sub {n : Nat} (left right : Poly n) : Poly n := add left (neg right)

def square {n : Nat} (poly : Poly n) : Poly n := mul poly poly

def pow {n : Nat} (poly : Poly n) : Nat → Poly n
  | 0 => const 1
  | k + 1 => mul (pow poly k) poly

def monomial {n : Nat} {R : Type*} [CommSemiring R]
    (x : Fin n → R) (e : Exp n) : R :=
  ∏ i, x i ^ e i

def evalTerm {n : Nat} (x : Fin n → ℝ) (term : Term n) : ℝ :=
  (term.coeff : ℝ) * monomial x term.exp

def eval {n : Nat} (x : Fin n → ℝ) (poly : Poly n) : ℝ :=
  (poly.map (evalTerm x)).sum

@[simp] theorem monomial_expAdd {n : Nat} {R : Type*} [CommSemiring R]
    (x : Fin n → R) (a b : Exp n) :
    monomial x (expAdd a b) = monomial x a * monomial x b := by
  simp only [monomial, expAdd, pow_add]
  exact Finset.prod_mul_distrib

@[simp] theorem eval_nil {n : Nat} (x : Fin n → ℝ) :
    eval x ([] : Poly n) = 0 := rfl

@[simp] theorem eval_cons {n : Nat} (x : Fin n → ℝ) (term : Term n) (poly : Poly n) :
    eval x (term :: poly) = evalTerm x term + eval x poly := by
  rfl

@[simp] theorem eval_append {n : Nat} (x : Fin n → ℝ) (left right : Poly n) :
    eval x (left ++ right) = eval x left + eval x right := by
  simp [eval, List.map_append, List.sum_append]

@[simp] theorem eval_insertTerm {n : Nat} (x : Fin n → ℝ) (term : Term n) (poly : Poly n) :
    eval x (insertTerm term poly) = evalTerm x term + eval x poly := by
  induction poly with
  | nil => simp [insertTerm]
  | cons head tail inductionHypothesis =>
      simp only [insertTerm]
      split
      · simp
      · split
        · rename_i equality
          simp only [eval_cons, evalTerm, equality, Rat.cast_add, add_mul]
          ring
        · simp [inductionHypothesis, add_assoc, add_left_comm]

@[simp] theorem eval_clean {n : Nat} (x : Fin n → ℝ) (poly : Poly n) :
    eval x (clean poly) = eval x poly := by
  induction poly with
  | nil => simp [clean]
  | cons head tail inductionHypothesis =>
      simp only [clean]
      split
      · rename_i coefficientZero
        simp [evalTerm, coefficientZero, inductionHypothesis]
      · simp [inductionHypothesis]

@[simp] theorem eval_foldr_insert {n : Nat} (x : Fin n → ℝ) (poly accumulator : Poly n) :
    eval x (poly.foldr insertTerm accumulator) = eval x poly + eval x accumulator := by
  induction poly with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp [List.foldr, inductionHypothesis, add_assoc]

@[simp] theorem eval_normalize {n : Nat} (x : Fin n → ℝ) (poly : Poly n) :
    eval x (normalize poly) = eval x poly := by
  rw [normalize, eval_clean, eval_foldr_insert, eval_nil, add_zero]
  exact ((List.mergeSort_perm poly termLE).map (evalTerm x)).sum_eq



@[simp] theorem eval_add {n : Nat} (x : Fin n → ℝ) (left right : Poly n) :
    eval x (add left right) = eval x left + eval x right := by
  simp [add]

@[simp] theorem eval_map_mulTerm {n : Nat} (x : Fin n → ℝ) (left : Term n) (right : Poly n) :
    eval x (right.map (mulTerm left)) = evalTerm x left * eval x right := by
  induction right with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, eval_cons, inductionHypothesis, eval_cons]
      simp only [evalTerm, mulTerm, Rat.cast_mul, monomial_expAdd]
      ring

@[simp] theorem eval_flatMap_mulTerm {n : Nat} (x : Fin n → ℝ)
    (left right : Poly n) :
    eval x (left.flatMap fun leftTerm => right.map (mulTerm leftTerm)) =
      eval x left * eval x right := by
  induction left with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis, add_mul]

@[simp] theorem eval_mulRaw {n : Nat} (x : Fin n → ℝ) (left right : Poly n) :
    eval x (mulRaw left right) = eval x left * eval x right := by
  simp [mulRaw]

@[simp] theorem eval_mul {n : Nat} (x : Fin n → ℝ) (left right : Poly n) :
    eval x (mul left right) = eval x left * eval x right := by
  simp [mul]

@[simp] theorem eval_const {n : Nat} (x : Fin n → ℝ) (coefficient : ℚ) :
    eval x (const coefficient : Poly n) = coefficient := by
  unfold const
  split
  · rename_i coefficientZero
    simp [coefficientZero]
  · simp [evalTerm, monomial, zeroExp]

@[simp] theorem eval_var {n : Nat} (x : Fin n → ℝ) (index : Fin n) :
    eval x (var index : Poly n) = x index := by
  simp [var, evalTerm, monomial, Finset.prod_ite_eq']

@[simp] theorem eval_map_scale {n : Nat} (x : Fin n → ℝ) (coefficient : ℚ)
    (poly : Poly n) :
    eval x (poly.map fun term => { term with coeff := coefficient * term.coeff }) =
      coefficient * eval x poly := by
  induction poly with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp [evalTerm, inductionHypothesis, mul_add, mul_assoc]

@[simp] theorem eval_scale {n : Nat} (x : Fin n → ℝ) (coefficient : ℚ)
    (poly : Poly n) : eval x (scale coefficient poly) = coefficient * eval x poly := by
  simp [scale]

@[simp] theorem eval_neg {n : Nat} (x : Fin n → ℝ) (poly : Poly n) :
    eval x (neg poly) = -eval x poly := by
  simp [neg]

@[simp] theorem eval_sub {n : Nat} (x : Fin n → ℝ) (left right : Poly n) :
    eval x (sub left right) = eval x left - eval x right := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem eval_square {n : Nat} (x : Fin n → ℝ) (poly : Poly n) :
    eval x (square poly) = eval x poly ^ 2 := by
  simp [square, pow_two]

@[simp] theorem eval_pow {n : Nat} (x : Fin n → ℝ) (poly : Poly n) :
    (k : Nat) → eval x (pow poly k) = eval x poly ^ k
  | 0 => by simp [pow]
  | k + 1 => by simp [pow, eval_pow x poly k, pow_succ]

@[simp] theorem mul_monoPoly {n : Nat} (left right : Exp n) :
    mul (monoPoly left) (monoPoly right) = monoPoly (expAdd left right) := by
  simp [mul, mulRaw, monoPoly, mulTerm]

@[simp] theorem scale_monoPoly {n : Nat} (coefficient : ℚ) (exponent : Exp n) :
    scale coefficient (monoPoly exponent) =
      [{ exp := exponent, coeff := coefficient }] := by
  simp [scale, monoPoly]

end SparsePolyCheck

namespace SparsePolyCheck

open scoped BigOperators

theorem weightedSquares_eq_gram {m r : Nat}
    (diagonal : Fin r → ℝ) (matrix : Fin m → Fin r → ℝ) (values : Fin m → ℝ) :
    (∑ pivot, diagonal pivot * (∑ row, matrix row pivot * values row) ^ 2) =
      ∑ row, ∑ column,
        (∑ pivot, diagonal pivot * matrix row pivot * matrix column pivot) *
          values row * values column := by
  calc
    (∑ pivot, diagonal pivot * (∑ row, matrix row pivot * values row) ^ 2) =
      ∑ pivot, ∑ row, ∑ column,
        diagonal pivot * (matrix row pivot * values row * (matrix column pivot * values column)) := by
          simp only [pow_two]
          simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ pivot, ∑ row, ∑ column,
        diagonal pivot * matrix row pivot * matrix column pivot * values row * values column := by
          apply Finset.sum_congr rfl
          intro pivot _
          apply Finset.sum_congr rfl
          intro row _
          apply Finset.sum_congr rfl
          intro column _
          ring
    _ = ∑ row, ∑ column, ∑ pivot,
        diagonal pivot * matrix row pivot * matrix column pivot * values row * values column := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro row _
          rw [Finset.sum_comm]
    _ = ∑ row, ∑ column,
        (∑ pivot, diagonal pivot * matrix row pivot * matrix column pivot) *
          values row * values column := by
          apply Finset.sum_congr rfl
          intro row _
          apply Finset.sum_congr rfl
          intro column _
          rw [Finset.sum_mul, Finset.sum_mul]

end SparsePolyCheck

namespace SparsePolyCheck

open scoped BigOperators

def sumPolys {n : Nat} : {m : Nat} → (Fin m → Poly n) → Poly n
  | 0, _ => []
  | m + 1, polys => add (polys 0) (sumPolys fun index => polys index.succ)

@[simp] theorem eval_sumPolys {n m : Nat} (x : Fin n → ℝ) (polys : Fin m → Poly n) :
    eval x (sumPolys polys) = ∑ index, eval x (polys index) := by
  induction m with
  | zero => simp [sumPolys]
  | succ m inductionHypothesis =>
      rw [sumPolys, eval_add, Fin.sum_univ_succ]
      simp [inductionHypothesis]

def gram {n m : Nat} (coefficients : Fin m → Fin m → ℚ)
    (basis : Fin m → Poly n) : Poly n :=
  sumPolys fun row => sumPolys fun column =>
    scale (coefficients row column) (mul (basis row) (basis column))

def gramRows {n m : Nat} (rows : List (Fin m))
    (coefficients : Fin m → Fin m → ℚ) (basis : Fin m → Poly n) : Poly n :=
  rows.foldr (fun row result =>
    add (sumPolys fun column =>
      scale (coefficients row column) (mul (basis row) (basis column))) result) []

@[simp] theorem gramRows_append {n m : Nat} (left right : List (Fin m))
    (coefficients : Fin m → Fin m → ℚ) (basis : Fin m → Poly n) :
    gramRows (left ++ right) coefficients basis =
      add (gramRows left coefficients basis) (gramRows right coefficients basis) := by
  induction left with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      simp only [List.cons_append, gramRows, List.foldr_cons, inductionHypothesis]
      simp [add, List.append_assoc]

def rectGram {n r m : Nat} (coefficients : Fin r → Fin m → ℚ)
    (rowBasis : Fin r → Poly n) (columnBasis : Fin m → Poly n) : Poly n :=
  sumPolys fun row => sumPolys fun column =>
    scale (coefficients row column) (mul (rowBasis row) (columnBasis column))

@[simp] theorem eval_gram {n m : Nat} (x : Fin n → ℝ)
    (coefficients : Fin m → Fin m → ℚ) (basis : Fin m → Poly n) :
    eval x (gram coefficients basis) =
      ∑ row, ∑ column, (coefficients row column : ℝ) *
        eval x (basis row) * eval x (basis column) := by
  simp [gram, mul_assoc]

@[simp] theorem eval_gramRows {n m : Nat} (x : Fin n → ℝ)
    (rows : List (Fin m)) (coefficients : Fin m → Fin m → ℚ)
    (basis : Fin m → Poly n) :
    eval x (gramRows rows coefficients basis) =
      (rows.map fun row => ∑ column, (coefficients row column : ℝ) *
        eval x (basis row) * eval x (basis column)).sum := by
  induction rows with
  | nil => simp [gramRows]
  | cons row rows inductionHypothesis =>
      change eval x
          (add (sumPolys fun column =>
            scale (coefficients row column) (mul (basis row) (basis column)))
            (gramRows rows coefficients basis)) = _
      rw [eval_add, eval_sumPolys, inductionHypothesis]
      simp [mul_assoc]

theorem eval_gramRows_all {n m : Nat} (x : Fin n → ℝ)
    (coefficients : Fin m → Fin m → ℚ) (basis : Fin m → Poly n) :
    eval x (gramRows (List.ofFn id) coefficients basis) =
      ∑ row, ∑ column, (coefficients row column : ℝ) *
        eval x (basis row) * eval x (basis column) := by
  rw [eval_gramRows]
  simp only [List.map_ofFn, Function.comp_id, List.sum_ofFn]

@[simp] theorem eval_rectGram {n r m : Nat} (x : Fin n → ℝ)
    (coefficients : Fin r → Fin m → ℚ)
    (rowBasis : Fin r → Poly n) (columnBasis : Fin m → Poly n) :
    eval x (rectGram coefficients rowBasis columnBasis) =
      ∑ row, ∑ column, (coefficients row column : ℝ) *
        eval x (rowBasis row) * eval x (columnBasis column) := by
  simp [rectGram, mul_assoc]

end SparsePolyCheck
