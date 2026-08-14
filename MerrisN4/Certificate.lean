import MerrisN4.Block0
import MerrisN4.Block1
import MerrisN4.Block2
import MerrisN4.Block3
import MerrisN4.TargetData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4.Certificate

open SparsePolyCheck FastPolyForSOS MerrisN4

/-- The polynomial representing the matrix cell with row-major index `index`. -/
def entry (index : Nat) : P :=
  entryPolys.getD index []

/-- The permanent of the symbolic doubly stochastic matrix in nine coordinates. -/
def permanentPoly : P :=
  fastSum
    [ fastProduct [entry 0, entry 5, entry 10, entry 15]
    , fastProduct [entry 0, entry 5, entry 11, entry 14]
    , fastProduct [entry 0, entry 6, entry 9, entry 15]
    , fastProduct [entry 0, entry 6, entry 11, entry 13]
    , fastProduct [entry 0, entry 7, entry 9, entry 14]
    , fastProduct [entry 0, entry 7, entry 10, entry 13]
    , fastProduct [entry 1, entry 4, entry 10, entry 15]
    , fastProduct [entry 1, entry 4, entry 11, entry 14]
    , fastProduct [entry 1, entry 6, entry 8, entry 15]
    , fastProduct [entry 1, entry 6, entry 11, entry 12]
    , fastProduct [entry 1, entry 7, entry 8, entry 14]
    , fastProduct [entry 1, entry 7, entry 10, entry 12]
    , fastProduct [entry 2, entry 4, entry 9, entry 15]
    , fastProduct [entry 2, entry 4, entry 11, entry 13]
    , fastProduct [entry 2, entry 5, entry 8, entry 15]
    , fastProduct [entry 2, entry 5, entry 11, entry 12]
    , fastProduct [entry 2, entry 7, entry 8, entry 13]
    , fastProduct [entry 2, entry 7, entry 9, entry 12]
    , fastProduct [entry 3, entry 4, entry 9, entry 14]
    , fastProduct [entry 3, entry 4, entry 10, entry 13]
    , fastProduct [entry 3, entry 5, entry 8, entry 14]
    , fastProduct [entry 3, entry 5, entry 10, entry 12]
    , fastProduct [entry 3, entry 6, entry 8, entry 13]
    , fastProduct [entry 3, entry 6, entry 9, entry 12]
    ]

def cubeSumPoly : P :=
  fastSum (entryPolys.map fun cell => FastPolyForSOS.fastPow cell 3)

/-- `24 * permanent - 2 - sum of entry cubes`, before expansion. -/
def compactTarget : P :=
  sub (sub (scale 24 permanentPoly) (const 2)) cubeSumPoly

/-- Sum of the four independently checked parts of the exact certificate. -/
def blocksTarget : P :=
  fastSum
    [ Block0Data.blockTarget
    , Block1Data.blockTarget
    , Block2Data.blockTarget
    , Block3Data.blockTarget
    ]

theorem normalized_blocksTarget :
    fastNormalize blocksTarget = TargetData.targetPoly := by
  native_decide

theorem normalized_compactTarget :
    fastNormalize compactTarget = TargetData.targetPoly := by
  native_decide

theorem eval_targetPoly_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x) :
    0 ≤ eval x TargetData.targetPoly := by
  have h0 := Block0.eval_blockTarget_nonneg x entriesNonnegative
  have h1 := Block1.eval_blockTarget_nonneg x entriesNonnegative
  have h2 := Block2.eval_blockTarget_nonneg x entriesNonnegative
  have h3 := Block3.eval_blockTarget_nonneg x entriesNonnegative
  have hblocks : 0 ≤ eval x blocksTarget := by
    simp only [blocksTarget, eval_fastSum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact add_nonneg h0 (add_nonneg h1 (add_nonneg h2 h3))
  have normalizedEvaluation := congrArg (eval x) normalized_blocksTarget
  rw [eval_fastNormalize] at normalizedEvaluation
  rw [← normalizedEvaluation]
  exact hblocks

theorem eval_compactTarget_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x) :
    0 ≤ eval x compactTarget := by
  have htarget := eval_targetPoly_nonneg x entriesNonnegative
  have normalizedEvaluation := congrArg (eval x) normalized_compactTarget
  rw [eval_fastNormalize] at normalizedEvaluation
  rw [normalizedEvaluation]
  exact htarget

end MerrisN4.Certificate
