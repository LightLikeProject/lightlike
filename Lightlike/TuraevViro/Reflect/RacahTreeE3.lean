import Lightlike.TuraevViro.Reflect.RacahCert0
import Lightlike.TuraevViro.Reflect.RacahCert2
import Lightlike.TuraevViro.Reflect.RacahCert4
import Lightlike.TuraevViro.Reflect.RacahCert6
import Lightlike.TuraevViro.Reflect.RacahCert8
import Lightlike.TuraevViro.Reflect.RacahCert10
import Lightlike.TuraevViro.Reflect.RacahCert12

import Lightlike.TuraevViro.Reflect.RacahBase

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

/-- The polynomial multiplying `c3` in the cleared recurrence identity. -/
def E3 : Poly := (neg (mul (mul ftwo fQ012) (add (mul [(⟨0, 0, 0, 0, 0, 0, 0, 0⟩, 1)] fW1) (neg (mul [(⟨0, 0, 0, 0, 0, 0, 0, 0⟩, 1)] fW0)))))
/-- The polynomial `E3`, written as a sum of certificate terms. -/
def bigE3 : Poly := (add (add (add (add (add (add (scale ((muInv.mul (Zk 0)), -2) B0_2) (scale ((muInv.mul (Zk 2)), -2) B2_2)) (scale ((muInv.mul (Zk 4)), -2) B4_2)) (scale ((muInv.mul (Zk 6)), -2) B6_2)) (scale ((muInv.mul (Zk 8)), -2) B8_2)) (scale ((muInv.mul (Zk 10)), -2) B10_2)) (scale ((muInv.mul (Zk 12)), -2) B12_1))
theorem tree_E3 : E3 = bigE3 := by decide +kernel

end Lightlike.TV.Refl
