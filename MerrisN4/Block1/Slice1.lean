import MerrisN4.MappingsData
import MerrisN4.Block1Base
import MerrisN4.Block1.Slice1Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4.Block1.Slice1

open SparsePolyCheck FastPolyForSOS MerrisN4
open MerrisN4.MappingsData
open MerrisN4.Block1Data

def mappings : List (List Nat) :=
  (cellMappings.drop 72).take 72

def certificate : P :=
  orbitCertificate mappings seedCells squares

def target : P :=
  Slice1Data.target

theorem normalized_certificate :
    fastNormalize certificate = target := by
  native_decide

theorem eval_target_nonneg (x : Fin 9 → ℝ)
    (entriesNonnegative : EntriesNonnegative x) :
    0 ≤ eval x target := by
  have normalizedEvaluation := congrArg (eval x) normalized_certificate
  rw [eval_fastNormalize] at normalizedEvaluation
  rw [← normalizedEvaluation]
  exact eval_orbitCertificate_nonneg x entriesNonnegative
    mappings seedCells squares Block1Base.weights_nonnegative

end MerrisN4.Block1.Slice1
