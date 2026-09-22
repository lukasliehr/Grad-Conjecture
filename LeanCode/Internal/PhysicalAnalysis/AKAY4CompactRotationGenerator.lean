import AKAY3PhaseMomentBounds
import QO17ScalarMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.Constraints Grad.PhysicalFamily
open Grad.GaugeCoefficients.Radial Grad.NonlinearQuotient

/-- The literal Cartesian rotation generator R=(Jy).grad on a real test. -/
def startupRotationDerivative (test : Spatial → ℝ) : Spatial → ℝ :=
  fun point => fderiv ℝ test point (planeQuarterTurn point)

theorem startupRotationDerivative_smooth (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) :
    ContDiff ℝ ∞ (startupRotationDerivative test) := by
  have derivative := (contDiff_infty_iff_fderiv.mp smooth).2
  exact derivative.clm_apply quarterTurnCLM.contDiff

theorem startupRotationDerivative_coordinates (test : Spatial → ℝ) (point : Spatial) :
    startupRotationDerivative test point =
      ∑ coordinate : Fin 2, planeQuarterTurn point coordinate * directionDerivative coordinate test point :=
  startupDerivative_coordinates (fderiv ℝ test point) (planeQuarterTurn point)

theorem startupRotationDerivative_supported (test : Spatial → ℝ) :
    tsupport (startupRotationDerivative test) ⊆ tsupport test := by
  apply closure_minimal _ (isClosed_tsupport test)
  intro point nonzero
  by_contra outside
  have derivativeZero : fderiv ℝ test point = 0 := by
    by_contra derivativeNonzero
    exact outside ((tsupport_fderiv_subset ℝ) (subset_closure derivativeNonzero))
  exact nonzero (by simp [startupRotationDerivative, derivativeZero])

def startupRotationTest (test : TestFunction openUnitDisk) : TestFunction openUnitDisk where
  toFun := startupRotationDerivative test.toFun
  smooth := startupRotationDerivative_smooth test.toFun test.smooth
  compact := test.compact.mono' (subset_closure.trans (startupRotationDerivative_supported test.toFun))
  supported := (startupRotationDerivative_supported test.toFun).trans test.supported

theorem startupRotation_quarter (angle : ℝ) (point : Spatial) :
    planeRotationEquiv angle (planeQuarterTurn point) =
      planeQuarterTurn (planeRotationEquiv angle point) := by
  ext coordinate
  fin_cases coordinate <;> simp [planeQuarterTurn, planeRotation] <;> ring

theorem startupInverseOrbit_hasDerivAt (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (point : Spatial) (angle : ℝ) :
    HasDerivAt (fun parameter => test (planeRotationEquiv (-parameter) point))
      (-startupRotationDerivative test (planeRotationEquiv (-angle) point)) angle := by
  have negative : HasDerivAt (fun parameter : ℝ => -parameter) (-1) angle := (hasDerivAt_id angle).neg
  have orbit := (Grad.NonlinearRange.planeRotationAction_hasDerivAt point (-angle)).scomp angle negative
  have derivative := (smooth.differentiable (by simp) (planeRotationEquiv (-angle) point)).hasFDerivAt
  have same : planeRotationAction (-angle) point = planeRotationEquiv (-angle) point :=
    physicalRotation_eq_orthogonal (-angle) point
  rw [← same] at derivative
  have composed := derivative.comp_hasDerivAt angle orbit
  simpa only [Function.comp_def, physicalRotation_eq_orthogonal, neg_smul, one_smul,
    map_neg, startupRotationDerivative] using composed

end Grad.CartesianStartup
