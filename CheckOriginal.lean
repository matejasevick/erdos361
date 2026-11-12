/-
Stage-A check: the three results that were verified before (independent of the new module
`Erdos361.Asymptotics`). Run with `lake env lean CheckOriginal.lean` after
`lake build Erdos361.Core Erdos361.InverseMain`. Expected output for each line:
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
import Erdos361.Core
import Erdos361.InverseMain

#print axioms Erdos361.erdos361_cge1
#print axioms Erdos361.erdos361_irregular
#print axioms Erdos361InverseMain.inverse_restricted
#print axioms Erdos361Freiman.freiman_3k3
