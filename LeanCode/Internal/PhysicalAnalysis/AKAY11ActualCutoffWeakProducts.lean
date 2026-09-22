import AKAY10ActualPhaseRemainderFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier

theorem startupCutoffL2_ae (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (field : StartupL2 3) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupCutoffL2 scalar smooth compact field point cell = (scalar point : ℂ) • field point cell :=
  fieldMultiplier_ae 3 openUnitDisk openUnitDisk_isOpen
    (derivativeScalar (compactSymbol 1 openUnitDisk scalar smooth compact) (zeroIndex 1)) field

theorem startupCutoffL2_pairing (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) :
    startupTestPairing cell vector test (startupCutoffL2 scalar smooth compact field) =
      startupTestPairing cell vector (multiplyTest scalar smooth test) field :=
  fieldMultiplier_pairing 3 openUnitDisk openUnitDisk_isOpen
    (derivativeScalar (compactSymbol 1 openUnitDisk scalar smooth compact) (zeroIndex 1)) field cell vector test

theorem startupDerivativeTest_multiply_two (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (test : TestFunction openUnitDisk) (outer inner : Fin 2) :
    startupDerivativeTest outer (startupDerivativeTest inner (multiplyTest scalar smooth test)) =
      startupAddTest
        (startupAddTest
          (startupAddTest
            (multiplyTest (directionDerivative outer (directionDerivative inner scalar))
              (startupTestDerivative_smooth _ (startupTestDerivative_smooth scalar smooth inner) outer) test)
            (multiplyTest (directionDerivative inner scalar)
              (startupTestDerivative_smooth scalar smooth inner) (startupDerivativeTest outer test)))
          (multiplyTest (directionDerivative outer scalar)
            (startupTestDerivative_smooth scalar smooth outer) (startupDerivativeTest inner test)))
        (multiplyTest scalar smooth (startupDerivativeTest outer (startupDerivativeTest inner test))) := by
  apply startupTest_ext
  intro point
  exact congrFun (startupDirection_mul_two scalar test.toFun smooth test.smooth outer inner) point

/-- Actual compact cutoff commutators use only L2 fields and genuine derivatives of the scalar. -/
theorem startupCutoffL2_second_test (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) (outer inner : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest inner
      (multiplyTest scalar smooth test))) field =
      startupTestPairing cell vector test
        (startupCutoffL2 (directionDerivative outer (directionDerivative inner scalar))
          (startupTestDerivative_smooth _ (startupTestDerivative_smooth scalar smooth inner) outer)
          (startupTestDerivative_compact _ (startupTestDerivative_compact scalar compact inner) outer) field) +
      startupTestPairing cell vector (startupDerivativeTest outer test)
        (startupCutoffL2 (directionDerivative inner scalar) (startupTestDerivative_smooth scalar smooth inner)
          (startupTestDerivative_compact scalar compact inner) field) +
      startupTestPairing cell vector (startupDerivativeTest inner test)
        (startupCutoffL2 (directionDerivative outer scalar) (startupTestDerivative_smooth scalar smooth outer)
          (startupTestDerivative_compact scalar compact outer) field) +
      startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest inner test))
        (startupCutoffL2 scalar smooth compact field) := by
  rw [startupDerivativeTest_multiply_two]
  simp only [startupTestPairing_add, add_apply, startupCutoffL2_pairing]

end Grad.CartesianStartup
