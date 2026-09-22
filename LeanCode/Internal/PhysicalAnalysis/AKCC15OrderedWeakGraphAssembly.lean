import AKCC10ActualFixedTensorWeakDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- Use the existing weighted-jet graph constructor on the literal weak
coordinates. This is only a change of carrier, not a new derivative assertion. -/
def startupGraphFromWeak {dimension order : ℕ} (field : StartupL2 dimension)
    (derivatives : JetIndex order → StartupL2 dimension)
    (zero : derivatives (zeroIndex order) = field)
    (weak : ∀ index, HasWeakOrderedDerivative dimension openUnitDisk (degree index) (derivativeWord index) field (derivatives index)) :
    GraphGrade dimension order 0 openUnitDisk :=
  ofCoordinates dimension order openUnitDisk (fun _ => 0) derivatives (by
    intro index cell vector test
    rw [Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply, zero,
      Grad.CellWeights.positiveFactor, pow_zero, mul_one, testPairing_apply, derivativeTestPairing_apply]
    exact (hasWeakOrderedDerivative_iff_integral dimension openUnitDisk (degree index) (derivativeWord index) field (derivatives index)).mp
      (weak index) cell vector test.toFun test.smooth test.compact test.supported)

theorem startupGraphFromWeak_base {dimension order : ℕ} (field : StartupL2 dimension)
    (derivatives : JetIndex order → StartupL2 dimension) (zero : derivatives (zeroIndex order) = field)
    (weak : ∀ index, HasWeakOrderedDerivative dimension openUnitDisk (degree index) (derivativeWord index) field (derivatives index)) :
    base dimension order openUnitDisk (fun _ => 0) (startupGraphFromWeak field derivatives zero weak) = field := by
  rw [base_apply, Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
  exact zero

end Grad.CartesianStartup
