import AKAX9ActualTrueInverseTensorWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

/-- Literal value-map transposition on every integer cell of the same rough field. -/
theorem startupTestPairing_valueMap (mapping : OperatorValue 3 3) (cell : ℤ)
    (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    (startupTestPairing cell vector test).comp (originalValueKernel mapping) =
      startupTestPairing cell (mapping.adjoint vector) test := by
  ext field
  simp only [ContinuousLinearMap.comp_apply, startupTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [startupPointKernel_coordinate_ae mapping (LinearIsometryEquiv.refl ℝ _) field cell,
    fieldCellProjection_ae 3 openUnitDisk (originalValueKernel mapping field)] with point actual projection
  change fieldCellProjection 3 openUnitDisk cell (originalValueKernel mapping field) point =
    mapping (field point cell) at actual
  rw [projection cell] at actual
  rw [actual]
  exact congrArg (fun scalar : ℂ => test.toFun point • scalar)
    (mapping.adjoint_inner_left (field point cell) vector).symm

/-- Exact mixed inverse tensor transposition after any fixed value map. -/
theorem startupValueTensor_mixedWeak (mapping : OperatorValue 3 3) (cell : ℤ)
    (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (field : StartupL2 3)
    (outer input : Fin 2) :
    startupTestPairing cell (mapping.adjoint vector) (startupDerivativeTest input
      (startupTrueInverseTest (startupDerivativeTest outer test))) field =
      ∑ output : Fin 2, startupTestPairing cell vector
        (startupDerivativeTest output (startupDerivativeTest outer test))
        (originalValueKernel mapping (startupTrueInverseTensorKernel input output field)) := by
  rw [startupTrueInverseTensor_mixedWeak]
  apply Finset.sum_congr rfl
  intro output _
  exact (congrArg (fun pairing : StartupL2 3 →L[ℂ] ℂ =>
      pairing (startupTrueInverseTensorKernel input output field))
    (startupTestPairing_valueMap mapping cell vector
      (startupDerivativeTest output (startupDerivativeTest outer test)))).symm

end Grad.CartesianStartup
