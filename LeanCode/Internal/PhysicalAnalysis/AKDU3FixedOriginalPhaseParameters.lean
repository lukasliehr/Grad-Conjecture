import AKDU2ActualProductCellFamily

noncomputable section
set_option autoImplicit false
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianState

/-- One original analytic width is chosen for the prescribed length before
all states, sources, iterations and regularity orders. It is never shrunk. -/
def mainPhaseParameters (length : ℝ) (positive : 0 < length) : PhaseParameters where
  length := length
  sigma0 := 1
  gamma := min (1/4) (Real.sqrt 5/(6*length))
  length_pos := positive
  sigma0_pos := by norm_num
  gamma_pos := lt_min (by norm_num) (div_pos (Real.sqrt_pos.mpr (by norm_num)) (mul_pos (by norm_num) positive))
  gamma_lt_min := by
    simp only [min_self]
    exact (min_le_left _ _).trans_lt (by norm_num)

theorem mainPhaseParameters_widthHalf (length : ℝ) (positive : 0 < length) :
    (mainPhaseParameters length positive).gamma ≤ 1/2 :=
  (min_le_left _ _).trans (by norm_num)

theorem mainPhaseParameters_widthLength (length : ℝ) (positive : 0 < length) :
    (mainPhaseParameters length positive).gamma ≤ Real.sqrt 5/(6*(mainPhaseParameters length positive).length) :=
  min_le_right _ _

end Grad.OriginalMainConsumer
