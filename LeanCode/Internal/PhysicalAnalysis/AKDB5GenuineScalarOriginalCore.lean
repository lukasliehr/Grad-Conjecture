import AKDB4SameWeightedNativeScalar
import AKCA23ActualScalarCartesianPolynomial
import AKBM9ActualProjectedPolarDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.NonlinearRange
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.OriginalKernelCovariantRecovery Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnnularOriginalSmoothCore
open Grad.OriginalKernelHomogeneousGraph

/-- Original-core polynomial contraction of the actual Cartesian covariant. -/
def scalarTangentialPolynomialCore (parameters : PhaseParameters) (covariant : ACore parameters 3) : ACore parameters 1 :=
  coordinateCore parameters 0 (valueMapCore parameters (matrixUnit (0 : Fin 1) (1 : Fin 3)) covariant) -
    coordinateCore parameters 1 (valueMapCore parameters (matrixUnit (0 : Fin 1) (0 : Fin 3)) covariant)

theorem scalarTangentialPolynomialCore_value (parameters : PhaseParameters) (covariant : ACore parameters 3)
    (point : ClosedDisk) (axial : ℝ) :
    coreValue (scalarTangentialPolynomialCore parameters covariant) point axial =
      scalarTangentialPolynomial point.val (coreValue covariant point axial) := by
  rw [scalarTangentialPolynomialCore,coreValue_subtract,coreValue_coordinate,coreValue_coordinate,
    coreValue_valueMap,coreValue_valueMap]
  rfl

/-- The genuine original scalar S=Xi+P[(Jy)·a_C], at unchanged analytic width. -/
def recoveredScalarOriginalCore (parameters : PhaseParameters) (covariant : ACore parameters 3)
    (xi : ACore parameters 1) : ACore parameters 1 :=
  xi + removeAngularCore parameters (scalarTangentialPolynomialCore parameters covariant)

theorem recoveredScalarOriginalCore_polar (parameters : PhaseParameters)
    (covariant : ACore parameters 3) (xi : ACore parameters 1)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (radius : Icc lower (1:ℝ)) (angles : ℝ×ℝ) :
    coreValue (recoveredScalarOriginalCore parameters covariant xi)
      (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) angles.2 =
    coreValue xi (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) angles.2 +
      removePolarMean (fun query => scalarTangentialPolynomial
        (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2).val
        (coreValue covariant (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2) query.2)) angles := by
  rw [recoveredScalarOriginalCore,coreValue_add,← originalCoreCircle_meanFree parameters lower positive bounded _ radius angles]
  congr 1
  congr 1
  funext query
  exact scalarTangentialPolynomialCore_value parameters covariant _ query.2

end Grad.OriginalCoreRealization
