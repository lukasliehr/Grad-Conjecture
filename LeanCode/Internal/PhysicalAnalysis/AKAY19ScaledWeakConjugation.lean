import AKAY18ScaledPhaseRemainderFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier Grad.AnalyticWeights.Calculus

theorem startupScaledPhaseFirstField_pairing (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (direction : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell • field point cell)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test (startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne direction moment) =
      startupTestPairing cell vector
        (multiplyTest (startupScaledPhaseSlope sigma gamma scale cell direction) (startupScaledPhaseSlope_smooth sigma gamma scale cell direction) test) field :=
  startupTestPairing_cellScalar _ (startupScaledPhaseSlope_smooth sigma gamma scale cell direction) cell vector test field _
    ((startupScaledPhaseFirstField_same sigma gamma scale nonnegative scaleNonnegative scaleOne direction field moment sameMoment).mono (fun _ same => same cell))

theorem startupScaledPhaseSecondField_pairing (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1) (outer inner : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell ^ 2 • field point cell)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test (startupScaledPhaseSecondField sigma gamma scale nonnegative scaleNonnegative scaleOne outer inner moment) =
      startupTestPairing cell vector
        (multiplyTest (startupScaledPhaseSecond sigma gamma scale cell outer inner) (startupScaledPhaseSecond_smooth sigma gamma scale cell outer inner) test) field :=
  startupTestPairing_cellScalar _ (startupScaledPhaseSecond_smooth sigma gamma scale cell outer inner) cell vector test field _
    ((startupScaledPhaseSecondField_same sigma gamma scale nonnegative scaleNonnegative scaleOne outer inner field moment sameMoment).mono (fun _ same => same cell))

theorem startupScaledConjugatedSecondTest (sigma gamma scale : ℝ) (cell : ℤ) (outer inner : Fin 2)
    (test : TestFunction openUnitDisk) :
    multiplyTest (inverseWeight sigma gamma scale cell) (smoothGoal sigma gamma scale cell).2.2
      (startupDerivativeTest outer (startupDerivativeTest inner
        (multiplyTest (physicalWeight sigma gamma scale cell) (smoothGoal sigma gamma scale cell).2.1 test))) =
      startupAddTest
        (startupAddTest
          (startupAddTest (startupDerivativeTest outer (startupDerivativeTest inner test))
            (multiplyTest (startupScaledPhaseSlope sigma gamma scale cell inner) (startupScaledPhaseSlope_smooth sigma gamma scale cell inner)
              (startupDerivativeTest outer test)))
          (multiplyTest (startupScaledPhaseSlope sigma gamma scale cell outer) (startupScaledPhaseSlope_smooth sigma gamma scale cell outer)
            (startupDerivativeTest inner test)))
        (multiplyTest (startupScaledPhaseSecond sigma gamma scale cell outer inner)
          (startupScaledPhaseSecond_smooth sigma gamma scale cell outer inner) test) := by
  apply startupTest_ext
  intro point
  exact startupScaledPhaseTest_second sigma gamma scale cell outer inner test point

/-- The genuine conjugated second derivative has exactly these L2/divergence remainders.
Every moment belongs to the SAME rough field, with no H1 input premise. -/
theorem startupScaledPhaseWeakSecond (sigma gamma scale : ℝ) (nonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (scaleOne : scale ≤ 1)
    (field firstMoment secondMoment : StartupL2 3)
    (firstSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      firstMoment point cell = Grad.CellWeights.cellWeight cell • field point cell)
    (secondSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      secondMoment point cell = Grad.CellWeights.cellWeight cell ^ 2 • field point cell)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (outer inner : Fin 2) :
    startupTestPairing cell vector
      (multiplyTest (inverseWeight sigma gamma scale cell) (smoothGoal sigma gamma scale cell).2.2
        (startupDerivativeTest outer (startupDerivativeTest inner
          (multiplyTest (physicalWeight sigma gamma scale cell) (smoothGoal sigma gamma scale cell).2.1 test)))) field =
      startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest inner test)) field +
      startupTestPairing cell vector (startupDerivativeTest outer test)
        (startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne inner firstMoment) +
      startupTestPairing cell vector (startupDerivativeTest inner test)
        (startupScaledPhaseFirstField sigma gamma scale nonnegative scaleNonnegative scaleOne outer firstMoment) +
      startupTestPairing cell vector test (startupScaledPhaseSecondField sigma gamma scale nonnegative scaleNonnegative scaleOne outer inner secondMoment) := by
  rw [startupScaledConjugatedSecondTest]
  simp only [startupTestPairing_add, add_apply,
    startupScaledPhaseFirstField_pairing sigma gamma scale nonnegative scaleNonnegative scaleOne _ field firstMoment firstSame,
    startupScaledPhaseSecondField_pairing sigma gamma scale nonnegative scaleNonnegative scaleOne _ _ field secondMoment secondSame]

end Grad.CartesianStartup
