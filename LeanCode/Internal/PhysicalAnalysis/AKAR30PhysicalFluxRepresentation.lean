import AKAR26SixActualAngularDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryLift Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularSmoothCore Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField

variable {parameters : PhaseParameters} {radius : RadialPoint}

def originalPolarRadialVector (value : ComplexEuclidean 1) (angle : ℝ) : ComplexEuclidean 3 :=
  matrixUnit 0 0 ((Real.cos angle : ℂ) • value)+matrixUnit 1 0 ((Real.sin angle : ℂ) • value)

theorem originalPolarRadialValue_continuous (source : ℝ × ℝ → ComplexEuclidean 3) (continuousSource : Continuous source) :
    Continuous (fun point => originalPolarRadialValue (source point) point.1) := by
  exact ((matrixUnit 0 0).continuous.comp ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).smul continuousSource)).add
    ((matrixUnit 0 1).continuous.comp ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_fst)).smul continuousSource))

theorem originalPolarTangentialValue_continuous (source : ℝ × ℝ → ComplexEuclidean 3) (continuousSource : Continuous source) :
    Continuous (fun point => originalPolarTangentialValue (source point) point.1) := by
  exact ((matrixUnit 0 1).continuous.comp ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).smul continuousSource)).sub
    ((matrixUnit 0 0).continuous.comp ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_fst)).smul continuousSource))

theorem originalPolarRadialVector_continuous (source : ℝ × ℝ → ComplexEuclidean 1) (continuousSource : Continuous source) :
    Continuous (fun point => originalPolarRadialVector (source point) point.1) := by
  exact ((matrixUnit 0 0).continuous.comp ((Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).smul continuousSource)).add
    ((matrixUnit 1 0).continuous.comp ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_fst)).smul continuousSource))

theorem OriginalCircleRepresents.radialColumn {field : CellL2 1} {source : ℝ × ℝ → ComplexEuclidean 1}
    (represented : OriginalCircleRepresents parameters radius field source) (continuousSource : Continuous source) :
    OriginalCircleRepresents parameters radius (originalCircleRadialColumn parameters field)
      (fun angles => originalPolarRadialVector (source angles) angles.1) := by
  exact ((represented.cosine continuousSource).valueMap (by fun_prop) (matrixUnit 0 0)).add
    ((represented.sine continuousSource).valueMap (by fun_prop) (matrixUnit 1 0)) (by fun_prop) (by fun_prop)

theorem OriginalCircleRepresents.meanFree {field : CellL2 1} {source : ℝ × ℝ → ComplexEuclidean 1}
    (represented : OriginalCircleRepresents parameters radius field source) (continuousSource : Continuous source) :
    OriginalCircleRepresents parameters radius (hilbertMeanFree parameters field) (removePolarMean source) := by
  intro mode
  unfold doubleCoefficient
  rw [doubleCoefficient_removePolarMean source continuousSource]
  change (_ : ℂ) • ((if mode.1=0 then (0:ℂ) else 1) • field mode) = _
  by_cases zero : mode.1=0
  · simp [zero]
  · simp only [zero,↓reduceIte,one_smul]
    exact represented mode

theorem OriginalCircleRotation.meanFree {field rotated : CellL2 1}
    (rotation : OriginalCircleRotation field rotated) : OriginalCircleRotation (hilbertMeanFree parameters field) rotated := by
  intro mode
  rw [rotation mode]
  change (_ : ℂ) • field mode = (_ : ℂ) • ((if mode.1=0 then (0:ℂ) else 1) • field mode)
  by_cases zero : mode.1=0 <;> simp [zero]

/-- Literal physical polar flux before the scalar mean projection. D is the
actual det(F_C) F_C^-1 family, and B the actual original cofactor metric. -/
def originalPhysicalRawFlux (parameters : PhaseParameters) (length epsilon : ℝ) (base : ACore parameters 3)
    (radius : RadialPoint) (vector : ℝ × ℝ → ComplexEuclidean 3) (xi : ℝ × ℝ → ComplexEuclidean 1)
    (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  originalPolarRadialValue
    (physicalMatrixProduct parameters (originalCofactorCovectorFamily parameters length epsilon base)
      radius.val radius.property.1 radius.property.2 vector angles) angles.1 +
  originalPolarTangentialValue
    (physicalMatrixProduct parameters (originalCofactorFamily parameters length epsilon base)
      radius.val radius.property.1 radius.property.2
      (fun point => originalPolarRadialVector ((radius.val : ℂ)⁻¹ • xi point) point.1) angles) angles.1

theorem originalPhysicalRawFlux_continuous (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint) (vector : ℝ × ℝ → ComplexEuclidean 3) (xi : ℝ × ℝ → ComplexEuclidean 1)
    (vectorContinuous : Continuous vector) (xiContinuous : Continuous xi) :
    Continuous (originalPhysicalRawFlux parameters length epsilon base radius vector xi) := by
  have low := (originalAxis_primitive_margin parameters length rho epsilon base small).1
  have one := physicalMatrixProduct_continuous parameters _
    (originalCofactorCovectorFamily_estimate parameters length rho epsilon base low).actualCoherent
    radius.val radius.property.1 radius.property.2 vector vectorContinuous
  have inner : Continuous (fun point => originalPolarRadialVector ((radius.val : ℂ)⁻¹ • xi point) point.1) := by
    exact originalPolarRadialVector_continuous _ (xiContinuous.const_smul ((radius.val : ℂ)⁻¹))
  have two := physicalMatrixProduct_continuous parameters _
    (originalCofactorFamily_estimate parameters length rho epsilon base low).actualCoherent
    radius.val radius.property.1 radius.property.2 _ inner
  exact (originalPolarRadialValue_continuous _ one).add (originalPolarTangentialValue_continuous _ two)

theorem originalPhysicalRawFlux_represents (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint) (vector : CellL2 3) (xi : CellL2 1)
    (vectorSource : ℝ × ℝ → ComplexEuclidean 3) (xiSource : ℝ × ℝ → ComplexEuclidean 1)
    (vectorContinuous : Continuous vectorSource) (xiContinuous : Continuous xiSource)
    (vectorRepresents : OriginalCircleRepresents parameters radius vector vectorSource)
    (xiRepresents : OriginalCircleRepresents parameters radius xi xiSource) :
    OriginalCircleRepresents parameters radius
      ((originalAxisCircleCoefficients parameters length rho epsilon base small radius).C vector+
        (originalAxisCircleCoefficients parameters length rho epsilon base small radius).kappa ((radius.val : ℂ)⁻¹ • xi))
      (originalPhysicalRawFlux parameters length epsilon base radius vectorSource xiSource) := by
  have low := (originalAxis_primitive_margin parameters length rho epsilon base small).1
  have one := vectorRepresents.matrix parameters _
    (originalCofactorCovectorFamily_estimate parameters length rho epsilon base low).actualCoherent radius vector vectorSource vectorContinuous
  have oneContinuous := physicalMatrixProduct_continuous parameters _
    (originalCofactorCovectorFamily_estimate parameters length rho epsilon base low).actualCoherent
    radius.val radius.property.1 radius.property.2 vectorSource vectorContinuous
  have scalarContinuous : Continuous (fun point => (radius.val : ℂ)⁻¹ • xiSource point) := xiContinuous.const_smul ((radius.val : ℂ)⁻¹)
  have radial := (xiRepresents.smul (radius.val : ℂ)⁻¹).radialColumn scalarContinuous
  have radialContinuous : Continuous (fun point => originalPolarRadialVector ((radius.val : ℂ)⁻¹ • xiSource point) point.1) := by
    exact originalPolarRadialVector_continuous _ scalarContinuous
  have two := radial.matrix parameters _
    (originalCofactorFamily_estimate parameters length rho epsilon base low).actualCoherent radius _ _ radialContinuous
  have twoContinuous := physicalMatrixProduct_continuous parameters _
    (originalCofactorFamily_estimate parameters length rho epsilon base low).actualCoherent
    radius.val radius.property.1 radius.property.2 _ radialContinuous
  exact (one.radial oneContinuous).add (two.tangential twoContinuous)
    (originalPolarRadialValue_continuous _ oneContinuous) (originalPolarTangentialValue_continuous _ twoContinuous)

end Grad.OriginalKernelRetainedDecay
