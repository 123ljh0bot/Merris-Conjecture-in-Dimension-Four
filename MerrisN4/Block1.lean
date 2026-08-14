import MerrisN4.Block1.Slice0
import MerrisN4.Block1.Slice1
import MerrisN4.Block1.Slice2
import MerrisN4.Block1.Slice3
import MerrisN4.Block1.Slice4
import MerrisN4.Block1.Slice5
import MerrisN4.Block1.Slice6
import MerrisN4.Block1.Slice7
import MerrisN4.Block1.Slice8
import MerrisN4.Block1.Slice9
import MerrisN4.Block1.Slice10
import MerrisN4.Block1.Slice11
import MerrisN4.Block1.Slice12
import MerrisN4.Block1.Slice13
import MerrisN4.Block1.Slice14
import MerrisN4.Block1.Slice15

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4.Block1

open SparsePolyCheck FastPolyForSOS MerrisN4
open MerrisN4.Block1Data

def sliceTargetSum : P :=
  fastSum
  [
    Block1.Slice0.target,
    Block1.Slice1.target,
    Block1.Slice2.target,
    Block1.Slice3.target,
    Block1.Slice4.target,
    Block1.Slice5.target,
    Block1.Slice6.target,
    Block1.Slice7.target,
    Block1.Slice8.target,
    Block1.Slice9.target,
    Block1.Slice10.target,
    Block1.Slice11.target,
    Block1.Slice12.target,
    Block1.Slice13.target,
    Block1.Slice14.target,
    Block1.Slice15.target
  ]

theorem normalized_slices :
    fastNormalize sliceTargetSum = blockTarget := by
  native_decide

theorem eval_blockTarget_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x) :
    0 ≤ eval x blockTarget := by
  have h0 := Block1.Slice0.eval_target_nonneg x entriesNonnegative
  have h1 := Block1.Slice1.eval_target_nonneg x entriesNonnegative
  have h2 := Block1.Slice2.eval_target_nonneg x entriesNonnegative
  have h3 := Block1.Slice3.eval_target_nonneg x entriesNonnegative
  have h4 := Block1.Slice4.eval_target_nonneg x entriesNonnegative
  have h5 := Block1.Slice5.eval_target_nonneg x entriesNonnegative
  have h6 := Block1.Slice6.eval_target_nonneg x entriesNonnegative
  have h7 := Block1.Slice7.eval_target_nonneg x entriesNonnegative
  have h8 := Block1.Slice8.eval_target_nonneg x entriesNonnegative
  have h9 := Block1.Slice9.eval_target_nonneg x entriesNonnegative
  have h10 := Block1.Slice10.eval_target_nonneg x entriesNonnegative
  have h11 := Block1.Slice11.eval_target_nonneg x entriesNonnegative
  have h12 := Block1.Slice12.eval_target_nonneg x entriesNonnegative
  have h13 := Block1.Slice13.eval_target_nonneg x entriesNonnegative
  have h14 := Block1.Slice14.eval_target_nonneg x entriesNonnegative
  have h15 := Block1.Slice15.eval_target_nonneg x entriesNonnegative
  have hsum : 0 ≤ eval x sliceTargetSum := by
    simp only [sliceTargetSum, eval_fastSum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact add_nonneg h0 (add_nonneg h1 (add_nonneg h2 (add_nonneg h3 (add_nonneg h4 (add_nonneg h5 (add_nonneg h6 (add_nonneg h7 (add_nonneg h8 (add_nonneg h9 (add_nonneg h10 (add_nonneg h11 (add_nonneg h12 (add_nonneg h13 (add_nonneg h14 (h15)))))))))))))))
  have normalizedEvaluation := congrArg (eval x) normalized_slices
  rw [eval_fastNormalize] at normalizedEvaluation
  rw [← normalizedEvaluation]
  exact hsum

end MerrisN4.Block1
