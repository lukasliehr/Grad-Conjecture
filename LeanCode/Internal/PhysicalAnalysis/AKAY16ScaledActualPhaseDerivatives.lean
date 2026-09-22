import AKAY15OriginalCompactWeakRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier
open Grad.AnalyticWeights.Calculus

/-- The derivative of the original square-root phase, at the actual admissible scale. -/
def startupScaledPhaseSlope (sigma gamma scale : ℝ) (cell : ℤ) (direction : Fin 2) : Spatial → ℝ :=
  directionDerivative direction (physicalPhase sigma gamma scale cell)

theorem startupScaledPhaseSlope_smooth (sigma gamma scale : ℝ) (cell : ℤ) (direction : Fin 2) :
    ContDiff ℝ ∞ (startupScaledPhaseSlope sigma gamma scale cell direction) :=
  startupTestDerivative_smooth _ (physicalPhase_contDiff sigma gamma scale cell) direction

theorem startupScaledPhysicalWeight_direction (sigma gamma scale : ℝ) (cell : ℤ) (direction : Fin 2) :
    directionDerivative direction (physicalWeight sigma gamma scale cell) =
      fun point => physicalWeight sigma gamma scale cell point * startupScaledPhaseSlope sigma gamma scale cell direction point := by
  funext point
  change fderiv ℝ (physicalWeight sigma gamma scale cell) point (spatialDirection direction) =
    physicalWeight sigma gamma scale cell point *
      fderiv ℝ (physicalPhase sigma gamma scale cell) point (spatialDirection direction)
  rw [(physicalWeight_hasFDerivAt sigma gamma scale cell point).fderiv,
    physicalPhase_fderiv]
  rfl

theorem startupScaledInverseWeight_direction (sigma gamma scale : ℝ) (cell : ℤ) (direction : Fin 2) :
    directionDerivative direction (inverseWeight sigma gamma scale cell) =
      fun point => -inverseWeight sigma gamma scale cell point * startupScaledPhaseSlope sigma gamma scale cell direction point := by
  funext point
  change fderiv ℝ (inverseWeight sigma gamma scale cell) point (spatialDirection direction) =
    -inverseWeight sigma gamma scale cell point *
      fderiv ℝ (physicalPhase sigma gamma scale cell) point (spatialDirection direction)
  rw [(inverseWeight_hasFDerivAt sigma gamma scale cell point).fderiv,
    physicalPhase_fderiv]
  rfl

/-- Both the genuine phase Hessian and the square of its gradient are retained. -/
def startupScaledPhaseSecond (sigma gamma scale : ℝ) (cell : ℤ) (outer inner : Fin 2) : Spatial → ℝ :=
  fun point => directionDerivative outer (startupScaledPhaseSlope sigma gamma scale cell inner) point +
    startupScaledPhaseSlope sigma gamma scale cell outer point * startupScaledPhaseSlope sigma gamma scale cell inner point

theorem startupScaledPhaseSecond_smooth (sigma gamma scale : ℝ) (cell : ℤ) (outer inner : Fin 2) :
    ContDiff ℝ ∞ (startupScaledPhaseSecond sigma gamma scale cell outer inner) :=
  (startupTestDerivative_smooth _ (startupScaledPhaseSlope_smooth sigma gamma scale cell inner) outer).add
    ((startupScaledPhaseSlope_smooth sigma gamma scale cell outer).mul (startupScaledPhaseSlope_smooth sigma gamma scale cell inner))

theorem startupScaledPhysicalWeight_two_directions (sigma gamma scale : ℝ) (cell : ℤ) (outer inner : Fin 2) :
    directionDerivative outer (directionDerivative inner (physicalWeight sigma gamma scale cell)) =
      fun point => physicalWeight sigma gamma scale cell point * startupScaledPhaseSecond sigma gamma scale cell outer inner point := by
  rw [startupScaledPhysicalWeight_direction]
  rw [startupDirection_mul (physicalWeight sigma gamma scale cell) (startupScaledPhaseSlope sigma gamma scale cell inner)
    (smoothGoal sigma gamma scale cell).2.1 (startupScaledPhaseSlope_smooth sigma gamma scale cell inner) outer,
    startupScaledPhysicalWeight_direction]
  funext point
  simp only [startupScaledPhaseSecond]
  ring

theorem startupScaledPhaseTest_first (sigma gamma scale : ℝ) (cell : ℤ) (direction : Fin 2)
    (test : TestFunction openUnitDisk) (point : Spatial) :
    inverseWeight sigma gamma scale cell point *
        (startupDerivativeTest direction
          (multiplyTest (physicalWeight sigma gamma scale cell) (smoothGoal sigma gamma scale cell).2.1 test)).toFun point =
      directionDerivative direction test.toFun point +
        startupScaledPhaseSlope sigma gamma scale cell direction point * test.toFun point := by
  change inverseWeight sigma gamma scale cell point *
    directionDerivative direction (fun source => physicalWeight sigma gamma scale cell source * test.toFun source) point = _
  rw [startupDirection_mul _ _ (smoothGoal sigma gamma scale cell).2.1 test.smooth direction,
    startupScaledPhysicalWeight_direction]
  have inverse : inverseWeight sigma gamma scale cell point * physicalWeight sigma gamma scale cell point = 1 := by
    rw [mul_comm]
    exact (formulaGoal sigma gamma scale cell point).2.2.2.2
  calc
    _ = (inverseWeight sigma gamma scale cell point * physicalWeight sigma gamma scale cell point) *
      (directionDerivative direction test.toFun point + startupScaledPhaseSlope sigma gamma scale cell direction point * test.toFun point) := by ring
    _ = _ := by rw [inverse, one_mul]

theorem startupScaledPhaseTest_second (sigma gamma scale : ℝ) (cell : ℤ) (outer inner : Fin 2)
    (test : TestFunction openUnitDisk) (point : Spatial) :
    inverseWeight sigma gamma scale cell point *
        (startupDerivativeTest outer (startupDerivativeTest inner
          (multiplyTest (physicalWeight sigma gamma scale cell) (smoothGoal sigma gamma scale cell).2.1 test))).toFun point =
      directionDerivative outer (directionDerivative inner test.toFun) point +
        startupScaledPhaseSlope sigma gamma scale cell inner point * directionDerivative outer test.toFun point +
        startupScaledPhaseSlope sigma gamma scale cell outer point * directionDerivative inner test.toFun point +
        startupScaledPhaseSecond sigma gamma scale cell outer inner point * test.toFun point := by
  change inverseWeight sigma gamma scale cell point *
    directionDerivative outer (directionDerivative inner
      (fun source => physicalWeight sigma gamma scale cell source * test.toFun source)) point = _
  rw [startupDirection_mul_two _ _ (smoothGoal sigma gamma scale cell).2.1 test.smooth outer inner,
    startupScaledPhysicalWeight_two_directions, startupScaledPhysicalWeight_direction, startupScaledPhysicalWeight_direction]
  have inverse : inverseWeight sigma gamma scale cell point * physicalWeight sigma gamma scale cell point = 1 := by
    rw [mul_comm]
    exact (formulaGoal sigma gamma scale cell point).2.2.2.2
  calc
    _ = (inverseWeight sigma gamma scale cell point * physicalWeight sigma gamma scale cell point) *
      (directionDerivative outer (directionDerivative inner test.toFun) point +
        startupScaledPhaseSlope sigma gamma scale cell inner point * directionDerivative outer test.toFun point +
        startupScaledPhaseSlope sigma gamma scale cell outer point * directionDerivative inner test.toFun point +
        startupScaledPhaseSecond sigma gamma scale cell outer inner point * test.toFun point) := by ring
    _ = _ := by rw [inverse, one_mul]

end Grad.CartesianStartup
