import MerrisN4.Block0Data

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace MerrisN4.Block0Base

open MerrisN4 MerrisN4.Block0Data

theorem weights_nonnegative : WeightsNonnegative squares := by
  apply weightsNonnegative_of_bool
  native_decide

end MerrisN4.Block0Base
