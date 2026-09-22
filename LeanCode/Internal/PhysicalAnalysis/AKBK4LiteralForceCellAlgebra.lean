import AKBK3SameNativeCovariantDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarCoefficients Grad.ActualCartesianEquations Grad.PDEBootstrap
open Grad.GaugeCoefficients.Physical.Ledger Grad.Constraints.Gauges Grad.PhysicalFamily

private def originalQuarterMap : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  matrixUnit (1 : Fin 3) (0 : Fin 3) - matrixUnit (0 : Fin 3) (1 : Fin 3)
private theorem originalQuarterMap_apply (value : ComplexEuclidean 3) :
    originalQuarterMap value = polarQuarter value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [originalQuarterMap,matrixUnit_apply,operatorBasis,polarQuarter]

private theorem planarPartMap_planarPart (value : ComplexEuclidean 3) :
    planarPartMap (planarPart value) = planarPartMap value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

/-- Axial Fourier selection commutes only with the fixed linear force algebra;
the complete coefficient correction is supplied before this operation. -/
theorem originalForceValue_axialCell (gradient rotation covariant correction : ℝ → ComplexEuclidean 3)
    (gradientContinuous : Continuous gradient) (rotationContinuous : Continuous rotation)
    (covariantContinuous : Continuous covariant) (correctionContinuous : Continuous correction) (cell : ℤ) :
    angularCoefficient (fun axial => planarPartMap (cartesianForceValue
      (gradient axial) (rotation axial) (covariant axial) (correction axial))) cell =
      planarPartMap (angularCoefficient gradient cell - angularCoefficient rotation cell -
        polarQuarter (angularCoefficient covariant cell) + angularCoefficient correction cell) := by
  have quarterContinuous : Continuous (fun axial => originalQuarterMap (covariant axial)) :=
    originalQuarterMap.continuous.comp covariantContinuous
  have same : (fun axial => planarPartMap (cartesianForceValue
      (gradient axial) (rotation axial) (covariant axial) (correction axial))) =
      fun axial => planarPartMap ((gradient axial - rotation axial - originalQuarterMap (covariant axial)) + correction axial) := by
    funext axial
    rw [cartesianForceValue,planarPartMap_planarPart,originalQuarterMap_apply]
  rw [same]
  have mapped := angularCoefficient_valueMap planarPartMap
    (fun axial => gradient axial - rotation axial - originalQuarterMap (covariant axial) + correction axial)
    (((gradientContinuous.sub rotationContinuous).sub quarterContinuous).add correctionContinuous) cell
  rw [mapped]
  have added := angularCoefficient_add_general
    (fun axial => gradient axial - rotation axial - originalQuarterMap (covariant axial)) correction
    ((gradientContinuous.sub rotationContinuous).sub quarterContinuous) correctionContinuous cell
  have subQuarter := angularCoefficient_sub_general (fun axial => gradient axial - rotation axial)
    (fun axial => originalQuarterMap (covariant axial)) (gradientContinuous.sub rotationContinuous) quarterContinuous cell
  have subRotation := angularCoefficient_sub_general gradient rotation gradientContinuous rotationContinuous cell
  have mappedQuarter := angularCoefficient_valueMap originalQuarterMap covariant covariantContinuous cell
  rw [added,subQuarter,subRotation,mappedQuarter,originalQuarterMap_apply]

/-- The genuine Cartesian scalar gradient of a fixed axial cell. -/
def nativeScalarGradient (xi : Spatial → ComplexEuclidean 1) (point : Spatial) : ComplexEuclidean 3 :=
  matrixUnit (0 : Fin 3) (0 : Fin 1) (fderiv ℝ xi point (spatialBasis 0)) +
    matrixUnit (1 : Fin 3) (0 : Fin 1) (fderiv ℝ xi point (spatialBasis 1))

private theorem planarGradientValue_units (derivative : Spatial × ℝ →L[ℝ] ComplexEuclidean 1) :
    planarGradientValue derivative =
      matrixUnit (0 : Fin 3) (0 : Fin 1) (derivative (spatialBasis 0,0)) +
        matrixUnit (1 : Fin 3) (0 : Fin 1) (derivative (spatialBasis 1,0)) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planarGradientValue,matrixUnit_apply,operatorBasis]

/-- The scalar gradient uses the already proved SAME cell derivatives. -/
theorem nativeScalarGradient_axialCell (xi : Spatial → ComplexEuclidean 1)
    (full : Spatial × ℝ → ComplexEuclidean 1) (cell : ℤ) (point : Spatial)
    (same : ∀ direction, fderiv ℝ xi point direction =
      angularCoefficient (fun axial => fderiv ℝ full (point,axial) (direction,0)) cell)
    (continuousDerivative : ∀ direction, Continuous (fun axial => fderiv ℝ full (point,axial) (direction,0))) :
    angularCoefficient (fun axial => planarGradientValue (fderiv ℝ full (point,axial))) cell =
      nativeScalarGradient xi point := by
  simp_rw [planarGradientValue_units]
  have added := angularCoefficient_add_general
    (fun axial => matrixUnit (0 : Fin 3) (0 : Fin 1) (fderiv ℝ full (point,axial) (spatialBasis 0,0)))
    (fun axial => matrixUnit (1 : Fin 3) (0 : Fin 1) (fderiv ℝ full (point,axial) (spatialBasis 1,0)))
    ((matrixUnit (0 : Fin 3) (0 : Fin 1)).continuous.comp (continuousDerivative (spatialBasis 0)))
    ((matrixUnit (1 : Fin 3) (0 : Fin 1)).continuous.comp (continuousDerivative (spatialBasis 1))) cell
  have first := angularCoefficient_valueMap (matrixUnit (0 : Fin 3) (0 : Fin 1))
    (fun axial => fderiv ℝ full (point,axial) (spatialBasis 0,0)) (continuousDerivative (spatialBasis 0)) cell
  have second := angularCoefficient_valueMap (matrixUnit (1 : Fin 3) (0 : Fin 1))
    (fun axial => fderiv ℝ full (point,axial) (spatialBasis 1,0)) (continuousDerivative (spatialBasis 1)) cell
  rw [added,first,second,nativeScalarGradient,same,same]

end Grad.ActualCartesianWeakEquations
