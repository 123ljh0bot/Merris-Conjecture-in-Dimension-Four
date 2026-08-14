import MerrisN4.Block0.Slice0
import MerrisN4.Block0.Slice1
import MerrisN4.Block0.Slice2
import MerrisN4.Block0.Slice3
import MerrisN4.Block0.Slice4
import MerrisN4.Block0.Slice5
import MerrisN4.Block0.Slice6
import MerrisN4.Block0.Slice7

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4.Block0

open SparsePolyCheck FastPolyForSOS MerrisN4
open MerrisN4.Block0Data

def sliceTargetSum : P :=
  fastSum
  [
    Block0.Slice0.target,
    Block0.Slice1.target,
    Block0.Slice2.target,
    Block0.Slice3.target,
    Block0.Slice4.target,
    Block0.Slice5.target,
    Block0.Slice6.target,
    Block0.Slice7.target
  ]

theorem normalized_slices :
    fastNormalize sliceTargetSum = blockTarget := by
  native_decide

theorem eval_blockTarget_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x) :
    0 ≤ eval x blockTarget := by
  have h0 := Block0.Slice0.eval_target_nonneg x entriesNonnegative
  have h1 := Block0.Slice1.eval_target_nonneg x entriesNonnegative
  have h2 := Block0.Slice2.eval_target_nonneg x entriesNonnegative
  have h3 := Block0.Slice3.eval_target_nonneg x entriesNonnegative
  have h4 := Block0.Slice4.eval_target_nonneg x entriesNonnegative
  have h5 := Block0.Slice5.eval_target_nonneg x entriesNonnegative
  have h6 := Block0.Slice6.eval_target_nonneg x entriesNonnegative
  have h7 := Block0.Slice7.eval_target_nonneg x entriesNonnegative
  have hsum : 0 ≤ eval x sliceTargetSum := by
    simp only [sliceTargetSum, eval_fastSum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact add_nonneg h0 (add_nonneg h1 (add_nonneg h2 (add_nonneg h3 (add_nonneg h4 (add_nonneg h5 (add_nonneg h6 (h7)))))))
  have normalizedEvaluation := congrArg (eval x) normalized_slices
  rw [eval_fastNormalize] at normalizedEvaluation
  rw [← normalizedEvaluation]
  exact hsum

end MerrisN4.Block0
