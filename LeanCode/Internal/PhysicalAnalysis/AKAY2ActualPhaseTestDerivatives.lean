import AKAY1CompactTestProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier
open Grad.AnalyticWeights.Calculus

/-- The derivative of the original square-root phase, at scale one. -/
def startupPhaseSlope (sigma gamma : ℝ) (cell : ℤ) (direction : Fin 2) : Spatial → ℝ :=
  directionDerivative direction (physicalPhase sigma gamma 1 cell)

theorem startupPhaseSlope_smooth (sigma gamma : ℝ) (cell : ℤ) (direction : Fin 2) :
    ContDiff ℝ ∞ (startupPhaseSlope sigma gamma cell direction) :=
  startupTestDerivative_smooth _ (physicalPhase_contDiff sigma gamma 1 cell) direction

theorem startupPhysicalWeight_direction (sigma gamma : ℝ) (cell : ℤ) (direction : Fin 2) :
    directionDerivative direction (physicalWeight sigma gamma 1 cell) =
      fun point => physicalWeight sigma gamma 1 cell point * startupPhaseSlope sigma gamma cell direction point := by
  funext point
  change fderiv ℝ (physicalWeight sigma gamma 1 cell) point (spatialDirection direction) =
    physicalWeight sigma gamma 1 cell point *
      fderiv ℝ (physicalPhase sigma gamma 1 cell) point (spatialDirection direction)
  rw [(physicalWeight_hasFDerivAt sigma gamma 1 cell point).fderiv,
    physicalPhase_fderiv]
  rfl

theorem startupInverseWeight_direction (sigma gamma : ℝ) (cell : ℤ) (direction : Fin 2) :
    directionDerivative direction (inverseWeight sigma gamma 1 cell) =
      fun point => -inverseWeight sigma gamma 1 cell point * startupPhaseSlope sigma gamma cell direction point := by
  funext point
  change fderiv ℝ (inverseWeight sigma gamma 1 cell) point (spatialDirection direction) =
    -inverseWeight sigma gamma 1 cell point *
      fderiv ℝ (physicalPhase sigma gamma 1 cell) point (spatialDirection direction)
  rw [(inverseWeight_hasFDerivAt sigma gamma 1 cell point).fderiv,
    physicalPhase_fderiv]
  rfl

/-- Both the genuine phase Hessian and the square of its gradient are retained. -/
def startupPhaseSecond (sigma gamma : ℝ) (cell : ℤ) (outer inner : Fin 2) : Spatial → ℝ :=
  fun point => directionDerivative outer (startupPhaseSlope sigma gamma cell inner) point +
    startupPhaseSlope sigma gamma cell outer point * startupPhaseSlope sigma gamma cell inner point

theorem startupPhaseSecond_smooth (sigma gamma : ℝ) (cell : ℤ) (outer inner : Fin 2) :
    ContDiff ℝ ∞ (startupPhaseSecond sigma gamma cell outer inner) :=
  (startupTestDerivative_smooth _ (startupPhaseSlope_smooth sigma gamma cell inner) outer).add
    ((startupPhaseSlope_smooth sigma gamma cell outer).mul (startupPhaseSlope_smooth sigma gamma cell inner))

theorem startupPhysicalWeight_two_directions (sigma gamma : ℝ) (cell : ℤ) (outer inner : Fin 2) :
    directionDerivative outer (directionDerivative inner (physicalWeight sigma gamma 1 cell)) =
      fun point => physicalWeight sigma gamma 1 cell point * startupPhaseSecond sigma gamma cell outer inner point := by
  rw [startupPhysicalWeight_direction]
  rw [startupDirection_mul (physicalWeight sigma gamma 1 cell) (startupPhaseSlope sigma gamma cell inner)
    (smoothGoal sigma gamma 1 cell).2.1 (startupPhaseSlope_smooth sigma gamma cell inner) outer,
    startupPhysicalWeight_direction]
  funext point
  simp only [startupPhaseSecond]
  ring

theorem startupPhaseTest_first (sigma gamma : ℝ) (cell : ℤ) (direction : Fin 2)
    (test : TestFunction openUnitDisk) (point : Spatial) :
    inverseWeight sigma gamma 1 cell point *
        (startupDerivativeTest direction
          (multiplyTest (physicalWeight sigma gamma 1 cell) (smoothGoal sigma gamma 1 cell).2.1 test)).toFun point =
      directionDerivative direction test.toFun point +
        startupPhaseSlope sigma gamma cell direction point * test.toFun point := by
  change inverseWeight sigma gamma 1 cell point *
    directionDerivative direction (fun source => physicalWeight sigma gamma 1 cell source * test.toFun source) point = _
  rw [startupDirection_mul _ _ (smoothGoal sigma gamma 1 cell).2.1 test.smooth direction,
    startupPhysicalWeight_direction]
  have inverse : inverseWeight sigma gamma 1 cell point * physicalWeight sigma gamma 1 cell point = 1 := by
    rw [mul_comm]
    exact (formulaGoal sigma gamma 1 cell point).2.2.2.2
  calc
    _ = (inverseWeight sigma gamma 1 cell point * physicalWeight sigma gamma 1 cell point) *
      (directionDerivative direction test.toFun point + startupPhaseSlope sigma gamma cell direction point * test.toFun point) := by ring
    _ = _ := by rw [inverse, one_mul]

theorem startupPhaseTest_second (sigma gamma : ℝ) (cell : ℤ) (outer inner : Fin 2)
    (test : TestFunction openUnitDisk) (point : Spatial) :
    inverseWeight sigma gamma 1 cell point *
        (startupDerivativeTest outer (startupDerivativeTest inner
          (multiplyTest (physicalWeight sigma gamma 1 cell) (smoothGoal sigma gamma 1 cell).2.1 test))).toFun point =
      directionDerivative outer (directionDerivative inner test.toFun) point +
        startupPhaseSlope sigma gamma cell inner point * directionDerivative outer test.toFun point +
        startupPhaseSlope sigma gamma cell outer point * directionDerivative inner test.toFun point +
        startupPhaseSecond sigma gamma cell outer inner point * test.toFun point := by
  change inverseWeight sigma gamma 1 cell point *
    directionDerivative outer (directionDerivative inner
      (fun source => physicalWeight sigma gamma 1 cell source * test.toFun source)) point = _
  rw [startupDirection_mul_two _ _ (smoothGoal sigma gamma 1 cell).2.1 test.smooth outer inner,
    startupPhysicalWeight_two_directions, startupPhysicalWeight_direction, startupPhysicalWeight_direction]
  have inverse : inverseWeight sigma gamma 1 cell point * physicalWeight sigma gamma 1 cell point = 1 := by
    rw [mul_comm]
    exact (formulaGoal sigma gamma 1 cell point).2.2.2.2
  calc
    _ = (inverseWeight sigma gamma 1 cell point * physicalWeight sigma gamma 1 cell point) *
      (directionDerivative outer (directionDerivative inner test.toFun) point +
        startupPhaseSlope sigma gamma cell inner point * directionDerivative outer test.toFun point +
        startupPhaseSlope sigma gamma cell outer point * directionDerivative inner test.toFun point +
        startupPhaseSecond sigma gamma cell outer inner point * test.toFun point) := by ring
    _ = _ := by rw [inverse, one_mul]

end Grad.CartesianStartup
