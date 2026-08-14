import MerrisN4.MappingsData
import MerrisN4.Block3Base
import MerrisN4.Block3.Slice21Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4.Block3.Slice21

open SparsePolyCheck FastPolyForSOS MerrisN4
open MerrisN4.MappingsData
open MerrisN4.Block3Data

def mappings : List (List Nat) :=
  (cellMappings.drop 1008).take 48

def certificate : P :=
  orbitCertificate mappings seedCells squares

def target : P :=
  Slice21Data.target

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
    mappings seedCells squares Block3Base.weights_nonnegative

end MerrisN4.Block3.Slice21
