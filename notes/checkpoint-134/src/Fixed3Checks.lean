import Fixed3
import FixedPool
import Move3
import MixedCertificate

namespace Checkpoint134.Fixed3
open PEqualNP.Outside.L_meta_9338 (ValidOn scanned combine)
set_option maxRecDepth 16000
set_option maxHeartbeats 0
def test (i : ℕ) := Accept book Move3.book 5 3 (tally book.coin (FixedPool.mask (Fin.ofNat 14 i))) (rank i)
private theorem checked0 : ValidOn test 0 14 := scanned _ 0 14 (by decide +kernel)
theorem allTests : ValidOn test 0 14 := checked0
theorem finiteChecks (i : FixedPool.Index) : Accept book Move3.book 5 3 (tally book.coin (FixedPool.mask i)) (rank i.val) = true := by
  have e := allTests i.val (Nat.zero_le _) i.isLt
  simpa only [test,Fin.ofNat_val_eq_self] using e
end Checkpoint134.Fixed3
