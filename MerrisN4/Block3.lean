import MerrisN4.Block3.Slice0
import MerrisN4.Block3.Slice1
import MerrisN4.Block3.Slice2
import MerrisN4.Block3.Slice3
import MerrisN4.Block3.Slice4
import MerrisN4.Block3.Slice5
import MerrisN4.Block3.Slice6
import MerrisN4.Block3.Slice7
import MerrisN4.Block3.Slice8
import MerrisN4.Block3.Slice9
import MerrisN4.Block3.Slice10
import MerrisN4.Block3.Slice11
import MerrisN4.Block3.Slice12
import MerrisN4.Block3.Slice13
import MerrisN4.Block3.Slice14
import MerrisN4.Block3.Slice15
import MerrisN4.Block3.Slice16
import MerrisN4.Block3.Slice17
import MerrisN4.Block3.Slice18
import MerrisN4.Block3.Slice19
import MerrisN4.Block3.Slice20
import MerrisN4.Block3.Slice21
import MerrisN4.Block3.Slice22
import MerrisN4.Block3.Slice23

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4.Block3

open SparsePolyCheck FastPolyForSOS MerrisN4
open MerrisN4.Block3Data

def sliceTargetSum : P :=
  fastSum
  [
    Block3.Slice0.target,
    Block3.Slice1.target,
    Block3.Slice2.target,
    Block3.Slice3.target,
    Block3.Slice4.target,
    Block3.Slice5.target,
    Block3.Slice6.target,
    Block3.Slice7.target,
    Block3.Slice8.target,
    Block3.Slice9.target,
    Block3.Slice10.target,
    Block3.Slice11.target,
    Block3.Slice12.target,
    Block3.Slice13.target,
    Block3.Slice14.target,
    Block3.Slice15.target,
    Block3.Slice16.target,
    Block3.Slice17.target,
    Block3.Slice18.target,
    Block3.Slice19.target,
    Block3.Slice20.target,
    Block3.Slice21.target,
    Block3.Slice22.target,
    Block3.Slice23.target
  ]

theorem normalized_slices :
    fastNormalize sliceTargetSum = blockTarget := by
  native_decide

theorem eval_blockTarget_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x) :
    0 ≤ eval x blockTarget := by
  have h0 := Block3.Slice0.eval_target_nonneg x entriesNonnegative
  have h1 := Block3.Slice1.eval_target_nonneg x entriesNonnegative
  have h2 := Block3.Slice2.eval_target_nonneg x entriesNonnegative
  have h3 := Block3.Slice3.eval_target_nonneg x entriesNonnegative
  have h4 := Block3.Slice4.eval_target_nonneg x entriesNonnegative
  have h5 := Block3.Slice5.eval_target_nonneg x entriesNonnegative
  have h6 := Block3.Slice6.eval_target_nonneg x entriesNonnegative
  have h7 := Block3.Slice7.eval_target_nonneg x entriesNonnegative
  have h8 := Block3.Slice8.eval_target_nonneg x entriesNonnegative
  have h9 := Block3.Slice9.eval_target_nonneg x entriesNonnegative
  have h10 := Block3.Slice10.eval_target_nonneg x entriesNonnegative
  have h11 := Block3.Slice11.eval_target_nonneg x entriesNonnegative
  have h12 := Block3.Slice12.eval_target_nonneg x entriesNonnegative
  have h13 := Block3.Slice13.eval_target_nonneg x entriesNonnegative
  have h14 := Block3.Slice14.eval_target_nonneg x entriesNonnegative
  have h15 := Block3.Slice15.eval_target_nonneg x entriesNonnegative
  have h16 := Block3.Slice16.eval_target_nonneg x entriesNonnegative
  have h17 := Block3.Slice17.eval_target_nonneg x entriesNonnegative
  have h18 := Block3.Slice18.eval_target_nonneg x entriesNonnegative
  have h19 := Block3.Slice19.eval_target_nonneg x entriesNonnegative
  have h20 := Block3.Slice20.eval_target_nonneg x entriesNonnegative
  have h21 := Block3.Slice21.eval_target_nonneg x entriesNonnegative
  have h22 := Block3.Slice22.eval_target_nonneg x entriesNonnegative
  have h23 := Block3.Slice23.eval_target_nonneg x entriesNonnegative
  have hsum : 0 ≤ eval x sliceTargetSum := by
    simp only [sliceTargetSum, eval_fastSum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact add_nonneg h0 (add_nonneg h1 (add_nonneg h2 (add_nonneg h3 (add_nonneg h4 (add_nonneg h5 (add_nonneg h6 (add_nonneg h7 (add_nonneg h8 (add_nonneg h9 (add_nonneg h10 (add_nonneg h11 (add_nonneg h12 (add_nonneg h13 (add_nonneg h14 (add_nonneg h15 (add_nonneg h16 (add_nonneg h17 (add_nonneg h18 (add_nonneg h19 (add_nonneg h20 (add_nonneg h21 (add_nonneg h22 (h23)))))))))))))))))))))))
  have normalizedEvaluation := congrArg (eval x) normalized_slices
  rw [eval_fastNormalize] at normalizedEvaluation
  rw [← normalizedEvaluation]
  exact hsum

end MerrisN4.Block3
