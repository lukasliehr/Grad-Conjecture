import AKCX41SameLocalizedEquationGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

namespace StartupSignedFamily
variable {L ell : ℝ} {order input output : ℕ}

theorem HasSpatialGrade.value {family : StartupSignedFamily input L ell} (regular : family.HasSpatialGrade order)
    (mapping : OperatorValue input output) : (family.value mapping).HasSpatialGrade order :=
  regular.map _ _ (originalValue_preservesGraph mapping)

theorem HasSpatialGrade.average {family : StartupSignedFamily 2 L ell} (regular : family.HasSpatialGrade order) :
    family.average.HasSpatialGrade order := regular.map _ _ originalAverage_preservesGraph

theorem HasSpatialGrade.primitive {family : StartupSignedFamily 2 L ell} (regular : family.HasSpatialGrade order) :
    family.primitive.HasSpatialGrade order := by
  have preserves : StartupPreservesGraph startupCovariantPrimitiveKernel := by
    unfold startupCovariantPrimitiveKernel startupCovariantAngularKernel startupRealAngularKernelDim
    exact (startupAngular_preservesGraph _ _ _).sub
      ((originalValue_preservesGraph quarterValueMap).comp (startupAngular_preservesGraph _ _ _))
  exact regular.map _ _ preserves

theorem HasSpatialGrade.trueInverse {family : StartupSignedFamily 1 L ell} (regular : family.HasSpatialGrade order) :
    family.trueInverse.HasSpatialGrade order := regular.map _ _ (startupTrueAngular_preservesGraph 1 0)

theorem HasSpatialGrade.recoveredGradient {vector right : StartupSignedFamily 2 L ell}
    (vectorRegular : vector.HasSpatialGrade order) (rightRegular : right.HasSpatialGrade order) :
    (vector.recoveredGradient right).HasSpatialGrade order :=
  (vectorRegular.sub vectorRegular.average).add ((rightRegular.add ((vectorRegular.value quarterValueMap).smul 2)).primitive)

theorem HasSpatialGrade.lowerFlux {lower : StartupSignedFamily 1 L ell} {gradient : StartupSignedFamily 2 L ell}
    (lowerRegular : lower.HasSpatialGrade order) (gradientRegular : gradient.HasSpatialGrade order) (direction : Fin 2) :
    (lower.lowerFlux gradient direction).HasSpatialGrade order := by
  unfold StartupSignedFamily.lowerFlux
  split_ifs
  · exact (((lowerRegular.value _).smul (-1)).add ((lowerRegular.trueInverse.value _).smul 2)).sub
      (gradientRegular.value _)
  · exact (((lowerRegular.trueInverse.value _).smul (-2)).sub (lowerRegular.value _)).sub
      (gradientRegular.value _)

theorem HasSpatialGrade.nativeLowerFlux {determinant scalar scalarFlux : StartupSignedFamily 1 L ell}
    {gradient : StartupSignedFamily 2 L ell}
    (detRegular : determinant.HasSpatialGrade order) (scalarRegular : scalar.HasSpatialGrade order)
    (fluxRegular : scalarFlux.HasSpatialGrade order) (gradientRegular : gradient.HasSpatialGrade order) (direction : Fin 2) :
    (nativeLowerFlux determinant scalar scalarFlux gradient direction).HasSpatialGrade order :=
  ((((detRegular.smul (-1)).sub (scalarRegular.shift 1)).add (fluxRegular.shift 1)).lowerFlux
    (gradientRegular.shift 1) direction)

end StartupSignedFamily
namespace StartupSignedAction
variable {L sigma gamma ell : ℝ}
variable (admissible : Admissible L sigma gamma ell) (data : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent data) (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible data.gaugeDeviation))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
include lengthNonzero scaleNonzero

theorem actualForce_allSpatialGrade (order : ℕ) (family : StartupSignedFamily 3 L ell) (regular : family.HasSpatialGrade order) :
    ((force admissible data coherent inverseCoherent).action family).HasSpatialGrade order :=
  (StartupSpatialAction.force admissible order data coherent inverseCoherent lengthNonzero scaleNonzero).preserves order family regular

theorem actualScalarFlux_allSpatialGrade (order : ℕ) (family : StartupSignedFamily 3 L ell) (regular : family.HasSpatialGrade order) :
    ((scalarFlux admissible data coherent inverseCoherent).action family).HasSpatialGrade order :=
  (StartupSpatialAction.scalarFlux admissible order data coherent inverseCoherent lengthNonzero scaleNonzero).preserves order family regular

end StartupSignedAction
end Grad.CartesianStartup
