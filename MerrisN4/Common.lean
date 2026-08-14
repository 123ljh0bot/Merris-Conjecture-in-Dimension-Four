import MerrisN4.FastPolyForSOS

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4

open SparsePolyCheck

abbrev P := Poly 9
abbrev Squares := List (ℚ × P)

def term (powers : List Nat) (coefficient : ℚ) : Term 9 :=
  { exp := fun index => powers.getD index.val 0, coeff := coefficient }

def fastSumImpl (polys : List P) : P :=
  FastPolyForSOS.addMany polys

@[implemented_by fastSumImpl] def fastSum : List P → P
  | [] => []
  | poly :: rest => FastPolyForSOS.fastAdd poly (fastSum rest)

def fastProduct : List P → P
  | [] => const 1
  | poly :: rest => FastPolyForSOS.fastMul poly (fastProduct rest)

def addPolyToMap (result : FastPolyForSOS.MapPoly) (poly : P) :
    FastPolyForSOS.MapPoly :=
  FastPolyForSOS.addMap result (FastPolyForSOS.ofPoly poly)

def fastSOSImpl (squares : Squares) : P :=
  FastPolyForSOS.toPoly 9 <|
    squares.foldl
      (fun result item =>
        addPolyToMap result
          (scale item.1 (FastPolyForSOS.fastSquare item.2)))
      ({} : FastPolyForSOS.MapPoly)

@[implemented_by fastSOSImpl] def fastSOS : Squares → P
  | [] => []
  | (weight, form) :: rest =>
      FastPolyForSOS.fastAdd
        (scale weight (FastPolyForSOS.fastSquare form))
        (fastSOS rest)

def entryPolys : List P :=
  [
    var 0,
    var 1,
    var 2,
    sub (const 1) (fastSum [var 0, var 1, var 2]),
    var 3,
    var 4,
    var 5,
    sub (const 1) (fastSum [var 3, var 4, var 5]),
    var 6,
    var 7,
    var 8,
    sub (const 1) (fastSum [var 6, var 7, var 8]),
    sub (const 1) (fastSum [var 0, var 3, var 6]),
    sub (const 1) (fastSum [var 1, var 4, var 7]),
    sub (const 1) (fastSum [var 2, var 5, var 8]),
    sub (fastSum [var 0, var 1, var 2, var 3, var 4, var 5, var 6, var 7, var 8])
      (const 2)
  ]

def variableCells : List Nat := [0, 1, 2, 4, 5, 6, 8, 9, 10]

def substitutionImages (mapping : List Nat) : List P :=
  variableCells.map fun cell =>
    entryPolys.getD (mapping.getD cell 0) []

def substituteMonomialImpl (images : List P) (exponent : Exp 9) : P :=
  (List.ofFn fun index : Fin 9 => index).foldl
    (fun result index =>
      let power := exponent index
      if power = 0 then result
      else
        FastPolyForSOS.fastMul result
          (FastPolyForSOS.fastPow (images.getD index.val []) power))
    (const 1)

@[implemented_by substituteMonomialImpl] def substituteMonomial
    (images : List P) (exponent : Exp 9) : P :=
  fastProduct (List.ofFn fun index =>
    FastPolyForSOS.fastPow (images.getD index.val []) (exponent index))

def substitutePolyImpl (mapping : List Nat) (poly : P) : P :=
  let images := substitutionImages mapping
  FastPolyForSOS.toPoly 9 <|
    poly.foldl
      (fun result item =>
        addPolyToMap result
          (scale item.coeff (substituteMonomial images item.exp)))
      ({} : FastPolyForSOS.MapPoly)

@[implemented_by substitutePolyImpl] def substitutePoly
    (mapping : List Nat) (poly : P) : P :=
  let images := substitutionImages mapping
  fastSum (poly.map fun item =>
    scale item.coeff (substituteMonomial images item.exp))

def transformSquares (mapping : List Nat) (squares : Squares) : Squares :=
  squares.map fun item => (item.1, substitutePoly mapping item.2)

def mappedCells (mapping cells : List Nat) : List Nat :=
  cells.map fun cell => mapping.getD cell 0

def cellProduct (mapping cells : List Nat) : P :=
  fastProduct ((mappedCells mapping cells).map fun cell =>
    entryPolys.getD cell [])

def transformedSOSImpl (mapping : List Nat) (squares : Squares) : P :=
  FastPolyForSOS.toPoly 9 <|
    squares.foldl
      (fun result item =>
        let transformed := substitutePolyImpl mapping item.2
        addPolyToMap result
          (scale item.1 (FastPolyForSOS.fastSquare transformed)))
      ({} : FastPolyForSOS.MapPoly)

def orbitTermImpl (seedCells mapping : List Nat) (squares : Squares) : P :=
  FastPolyForSOS.fastMul
    (cellProduct mapping seedCells)
    (transformedSOSImpl mapping squares)

@[implemented_by orbitTermImpl] def orbitTerm
    (seedCells mapping : List Nat) (squares : Squares) : P :=
  FastPolyForSOS.fastMul
    (cellProduct mapping seedCells)
    (fastSOS (transformSquares mapping squares))

def orbitCertificateImpl
    (mappings : List (List Nat)) (seedCells : List Nat) (squares : Squares) : P :=
  FastPolyForSOS.toPoly 9 <|
    squares.foldl
      (fun result item =>
        let orbit := FastPolyForSOS.toPoly 9 <|
          mappings.foldl
            (fun orbitResult mapping =>
              let transformed := substitutePolyImpl mapping item.2
              let term := FastPolyForSOS.fastMul
                (cellProduct mapping seedCells)
                (FastPolyForSOS.fastSquare transformed)
              addPolyToMap orbitResult term)
            ({} : FastPolyForSOS.MapPoly)
        addPolyToMap result (scale item.1 orbit))
      ({} : FastPolyForSOS.MapPoly)

@[implemented_by orbitCertificateImpl] def orbitCertificate :
    List (List Nat) → List Nat → Squares → P
  | [], _, _ => []
  | mapping :: mappings, seedCells, squares =>
      FastPolyForSOS.fastAdd
        (orbitTerm seedCells mapping squares)
        (orbitCertificate mappings seedCells squares)

def WeightsNonnegative (squares : Squares) : Prop :=
  ∀ item ∈ squares, 0 ≤ item.1

def weightsNonnegativeBool (squares : Squares) : Bool :=
  squares.all fun item => decide (0 ≤ item.1)

theorem weightsNonnegative_of_bool (squares : Squares)
    (result : weightsNonnegativeBool squares = true) :
    WeightsNonnegative squares := by
  intro item itemInSquares
  have allResult : ∀ source ∈ squares, decide (0 ≤ source.1) = true := by
    simpa [weightsNonnegativeBool, List.all_eq_true] using result
  exact of_decide_eq_true (allResult item itemInSquares)

@[simp] theorem eval_fastSum (x : Fin 9 → ℝ) (polys : List P) :
    eval x (fastSum polys) = (polys.map (eval x)).sum := by
  induction polys with
  | nil => simp [fastSum]
  | cons poly rest inductionHypothesis =>
      simp [fastSum, inductionHypothesis]

@[simp] theorem eval_fastProduct (x : Fin 9 → ℝ) (polys : List P) :
    eval x (fastProduct polys) = (polys.map (eval x)).prod := by
  induction polys with
  | nil => simp [fastProduct]
  | cons poly rest inductionHypothesis =>
      simp [fastProduct, inductionHypothesis]

theorem eval_fastSOS_nonneg (x : Fin 9 → ℝ) (squares : Squares)
    (weightsNonnegative : WeightsNonnegative squares) :
    0 ≤ eval x (fastSOS squares) := by
  induction squares with
  | nil => simp [fastSOS]
  | cons item rest inductionHypothesis =>
      rcases item with ⟨weight, form⟩
      rw [fastSOS, FastPolyForSOS.eval_fastAdd, eval_scale,
        FastPolyForSOS.eval_fastSquare]
      apply add_nonneg
      · exact mul_nonneg
          (Rat.cast_nonneg.mpr
            (weightsNonnegative (weight, form) (by simp)))
          (sq_nonneg _)
      · apply inductionHypothesis
        intro source sourceInRest
        exact weightsNonnegative source (by simp [sourceInRest])

theorem weightsNonnegative_transform (mapping : List Nat) (squares : Squares)
    (weightsNonnegative : WeightsNonnegative squares) :
    WeightsNonnegative (transformSquares mapping squares) := by
  intro item itemInTransformed
  simp only [transformSquares, List.mem_map] at itemInTransformed
  obtain ⟨source, sourceInSquares, sourceImage⟩ := itemInTransformed
  rcases source with ⟨weight, form⟩
  simp only at sourceImage
  subst item
  exact weightsNonnegative (weight, form) sourceInSquares

def EntriesNonnegative (x : Fin 9 → ℝ) : Prop :=
  ∀ index : Nat, 0 ≤ eval x (entryPolys.getD index [])

theorem eval_cellProduct_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x)
    (mapping cells : List Nat) :
    0 ≤ eval x (cellProduct mapping cells) := by
  rw [cellProduct, eval_fastProduct]
  apply List.prod_nonneg
  intro value valueIn
  obtain ⟨poly, polyIn, rfl⟩ := List.mem_map.mp valueIn
  obtain ⟨cell, _, rfl⟩ := List.mem_map.mp polyIn
  exact entriesNonnegative _

theorem eval_orbitTerm_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x)
    (seedCells mapping : List Nat) (squares : Squares)
    (weightsNonnegative : WeightsNonnegative squares) :
    0 ≤ eval x (orbitTerm seedCells mapping squares) := by
  rw [orbitTerm, FastPolyForSOS.eval_fastMul]
  exact mul_nonneg
    (eval_cellProduct_nonneg x entriesNonnegative mapping seedCells)
    (eval_fastSOS_nonneg x _
      (weightsNonnegative_transform mapping squares weightsNonnegative))

theorem eval_orbitCertificate_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x)
    (mappings : List (List Nat)) (seedCells : List Nat) (squares : Squares)
    (weightsNonnegative : WeightsNonnegative squares) :
    0 ≤ eval x (orbitCertificate mappings seedCells squares) := by
  induction mappings with
  | nil => simp [orbitCertificate]
  | cons mapping mappings inductionHypothesis =>
      rw [orbitCertificate, FastPolyForSOS.eval_fastAdd]
      exact add_nonneg
        (eval_orbitTerm_nonneg x entriesNonnegative seedCells mapping squares
          weightsNonnegative)
        inductionHypothesis

end MerrisN4
