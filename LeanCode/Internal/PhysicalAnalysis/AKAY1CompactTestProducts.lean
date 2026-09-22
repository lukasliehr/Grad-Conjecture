import AKAX17OriginalERPrincipalWeakConsumer
import AW2Weights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier

theorem startupDirection_mul (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (direction : Fin 2) :
    directionDerivative direction (fun point => first point * second point) =
      fun point => directionDerivative direction first point * second point +
        first point * directionDerivative direction second point := by
  funext point
  change fderiv ℝ (first * second) point (spatialDirection direction) =
    fderiv ℝ first point (spatialDirection direction) * second point +
      first point * fderiv ℝ second point (spatialDirection direction)
  rw [fderiv_mul (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem startupDirection_add (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (direction : Fin 2) :
    directionDerivative direction (fun point => first point + second point) =
      fun point => directionDerivative direction first point +
        directionDerivative direction second point := by
  funext point
  change fderiv ℝ (first + second) point (spatialDirection direction) =
    fderiv ℝ first point (spatialDirection direction) + fderiv ℝ second point (spatialDirection direction)
  rw [fderiv_add (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

theorem startupDirection_mul_two (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (outer inner : Fin 2) :
    directionDerivative outer (directionDerivative inner (fun point => first point * second point)) =
      fun point =>
        directionDerivative outer (directionDerivative inner first) point * second point +
        directionDerivative inner first point * directionDerivative outer second point +
        directionDerivative outer first point * directionDerivative inner second point +
        first point * directionDerivative outer (directionDerivative inner second) point := by
  rw [startupDirection_mul first second firstSmooth secondSmooth inner]
  rw [startupDirection_add
    (fun point => directionDerivative inner first point * second point)
    (fun point => first point * directionDerivative inner second point)
    ((startupTestDerivative_smooth first firstSmooth inner).mul secondSmooth)
    (firstSmooth.mul (startupTestDerivative_smooth second secondSmooth inner)) outer]
  rw [startupDirection_mul (directionDerivative inner first) second
    (startupTestDerivative_smooth first firstSmooth inner) secondSmooth outer]
  rw [startupDirection_mul first (directionDerivative inner second) firstSmooth
    (startupTestDerivative_smooth second secondSmooth inner) outer]
  funext point
  ring

theorem startupDerivativeTest_multiply (scalar : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ scalar) (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupDerivativeTest direction (multiplyTest scalar smooth test) =
      startupAddTest
        (multiplyTest (directionDerivative direction scalar)
          (startupTestDerivative_smooth scalar smooth direction) test)
        (multiplyTest scalar smooth (startupDerivativeTest direction test)) := by
  apply startupTest_ext
  intro point
  exact congrFun (startupDirection_mul scalar test.toFun smooth test.smooth direction) point

end Grad.CartesianStartup
