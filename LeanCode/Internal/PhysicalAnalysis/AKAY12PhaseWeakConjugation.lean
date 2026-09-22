import AKAY11ActualCutoffWeakProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier Grad.AnalyticWeights.Calculus

theorem startupTestPairing_cellScalar (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (field multiplied : StartupL2 3)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, multiplied point cell = scalar point • field point cell) :
    startupTestPairing cell vector test multiplied =
      startupTestPairing cell vector (multiplyTest scalar smooth test) field := by
  rw [startupTestPairing_apply, startupTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [same] with point same
  rw [same]
  have linear := (innerSL ℂ vector).toLinearMap.map_smul_of_tower (scalar point) (field point cell)
  change inner ℂ vector (scalar point • field point cell) = scalar point • inner ℂ vector (field point cell) at linear
  rw [linear]
  change test.toFun point • (scalar point • inner ℂ vector (field point cell)) =
    (scalar point * test.toFun point) • inner ℂ vector (field point cell)
  rw [smul_smul, mul_comm]

theorem startupPhaseFirstField_pairing (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (direction : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell • field point cell)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test (startupPhaseFirstField sigma gamma nonnegative direction moment) =
      startupTestPairing cell vector
        (multiplyTest (startupPhaseSlope sigma gamma cell direction) (startupPhaseSlope_smooth sigma gamma cell direction) test) field :=
  startupTestPairing_cellScalar _ (startupPhaseSlope_smooth sigma gamma cell direction) cell vector test field _
    ((startupPhaseFirstField_same sigma gamma nonnegative direction field moment sameMoment).mono (fun _ same => same cell))

theorem startupPhaseSecondField_pairing (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma) (outer inner : Fin 2)
    (field moment : StartupL2 3)
    (sameMoment : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = Grad.CellWeights.cellWeight cell ^ 2 • field point cell)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test (startupPhaseSecondField sigma gamma nonnegative outer inner moment) =
      startupTestPairing cell vector
        (multiplyTest (startupPhaseSecond sigma gamma cell outer inner) (startupPhaseSecond_smooth sigma gamma cell outer inner) test) field :=
  startupTestPairing_cellScalar _ (startupPhaseSecond_smooth sigma gamma cell outer inner) cell vector test field _
    ((startupPhaseSecondField_same sigma gamma nonnegative outer inner field moment sameMoment).mono (fun _ same => same cell))

theorem startupConjugatedSecondTest (sigma gamma : ℝ) (cell : ℤ) (outer inner : Fin 2)
    (test : TestFunction openUnitDisk) :
    multiplyTest (inverseWeight sigma gamma 1 cell) (smoothGoal sigma gamma 1 cell).2.2
      (startupDerivativeTest outer (startupDerivativeTest inner
        (multiplyTest (physicalWeight sigma gamma 1 cell) (smoothGoal sigma gamma 1 cell).2.1 test))) =
      startupAddTest
        (startupAddTest
          (startupAddTest (startupDerivativeTest outer (startupDerivativeTest inner test))
            (multiplyTest (startupPhaseSlope sigma gamma cell inner) (startupPhaseSlope_smooth sigma gamma cell inner)
              (startupDerivativeTest outer test)))
          (multiplyTest (startupPhaseSlope sigma gamma cell outer) (startupPhaseSlope_smooth sigma gamma cell outer)
            (startupDerivativeTest inner test)))
        (multiplyTest (startupPhaseSecond sigma gamma cell outer inner)
          (startupPhaseSecond_smooth sigma gamma cell outer inner) test) := by
  apply startupTest_ext
  intro point
  exact startupPhaseTest_second sigma gamma cell outer inner test point

/-- The genuine conjugated second derivative has exactly these L2/divergence remainders.
Every moment belongs to the SAME rough field, with no H1 input premise. -/
theorem startupPhaseWeakSecond (sigma gamma : ℝ) (nonnegative : 0 ≤ gamma)
    (field firstMoment secondMoment : StartupL2 3)
    (firstSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      firstMoment point cell = Grad.CellWeights.cellWeight cell • field point cell)
    (secondSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      secondMoment point cell = Grad.CellWeights.cellWeight cell ^ 2 • field point cell)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (outer inner : Fin 2) :
    startupTestPairing cell vector
      (multiplyTest (inverseWeight sigma gamma 1 cell) (smoothGoal sigma gamma 1 cell).2.2
        (startupDerivativeTest outer (startupDerivativeTest inner
          (multiplyTest (physicalWeight sigma gamma 1 cell) (smoothGoal sigma gamma 1 cell).2.1 test)))) field =
      startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest inner test)) field +
      startupTestPairing cell vector (startupDerivativeTest outer test)
        (startupPhaseFirstField sigma gamma nonnegative inner firstMoment) +
      startupTestPairing cell vector (startupDerivativeTest inner test)
        (startupPhaseFirstField sigma gamma nonnegative outer firstMoment) +
      startupTestPairing cell vector test (startupPhaseSecondField sigma gamma nonnegative outer inner secondMoment) := by
  rw [startupConjugatedSecondTest]
  simp only [startupTestPairing_add, add_apply,
    startupPhaseFirstField_pairing sigma gamma nonnegative _ field firstMoment firstSame,
    startupPhaseSecondField_pairing sigma gamma nonnegative _ _ field secondMoment secondSame]

end Grad.CartesianStartup
