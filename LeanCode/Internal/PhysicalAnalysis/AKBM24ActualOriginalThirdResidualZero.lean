import AKBM23SameOriginalProjectedAxialFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set Filter
open scoped Topology
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualPolarFlux
open Grad.ActualPolarEquations Grad.ActualCartesianEquations Grad.SourceCollarFullSource
open Grad.NonlinearRange
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.Constraints Grad.Cor18
open Grad.OriginalKernelCovariantRecovery Grad.AnnularPhysicalReconstruction Grad.ActualDeterminantEquations
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift

variable (parameters : PhaseParameters) (compact : ℝ) (nonzero : parameters.length≠0)
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)


include nonzero sameBase sameEpsilon constrained homogeneous



/-- The computed G3 residual of the SAME original physical homogeneous
field is zero. No scalar residual or graph-equation assumption is supplied. -/
theorem originalHomogeneous_tupleG3_zero (radius : Icc lower (1:ℝ)) (interior : radius.val∈Ioo lower 1) (mode : ℤ×ℤ) :
    originalTupleG3 parameters parameters.length compact lower positive state
      (originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar) radius mode=0 := by
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let seven := originalKernelSevenCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let tuple := originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let bThree := seven.bThree parameters parameters.length compact lower positive bounded state
  let axial := (originalDifferentiatedCurves bThree bounded true).2.meanFree
  let retained := seven.lowPhysicalCurves parameters parameters.length compact lower positive bounded state 2
  let rhs := ((pressure.smul (-((radius.val:ℂ)⁻¹))).sub (axial.smul (parameters.length:ℂ)⁻¹)).sub
    (retained.smul (radius.val:ℂ)⁻¹)
  let slopes := fun query => derivWithin (fun location => originalPhysicalCoefficient (tuple.val 0) location query) (Icc lower 1) radius.val
  have derivatives (query : ℤ×ℤ) : HasDerivWithinAt (fun location => pressure.physicalCurve 0 location query)
      (slopes query) (Icc lower 1) radius.val := by
    have actual := originalTuple_coefficient_derivative parameters lower bounded tuple 0 query radius.val radius.property
    rw [originalTupleSlopeCurve_same parameters lower bounded tuple 0 query radius.val radius.property] at actual
    apply actual.congr
    · intro location member
      exact (pressure.fullField_coefficient bounded location member query).symm
    · exact (pressure.fullField_coefficient bounded radius.val radius.property query).symm
  have pointwise (angles : ℝ×ℝ) : WithLp.toLp 2 (fun _ : Fin 1 =>
      scalarDirectionalField pressure bounded 0 (1,0,0) (radius.val,angles))=rhs.fullField bounded (radius.val,angles) := by
    have actual := originalHomogeneous_correctedScalar_zero parameters compact nonzero state small insideSeed lower positive bounded
      physicalState sameBase sameEpsilon vector scalar constrained homogeneous radius.val interior angles
    dsimp only at actual
    rw [originalProjectedAxial_fullField _ bounded radius.val interior angles] at actual
    dsimp only [rhs]
    rw [SmoothLowPhysicalRow.fullField_sub _ bounded _ radius.val radius.property angles,
      SmoothLowPhysicalRow.fullField_sub _ bounded _ radius.val radius.property angles,
      samePhysical_fullField_smul _ bounded _ radius.val radius.property angles,
      samePhysical_fullField_smul _ bounded _ radius.val radius.property angles,
      samePhysical_fullField_smul _ bounded _ radius.val radius.property angles]
    apply PiLp.ext
    intro component
    fin_cases component
    change scalarDirectionalField pressure bounded 0 (1,0,0) (radius.val,angles)=
      -(radius.val:ℂ)⁻¹*pressure.fullField bounded (radius.val,angles) 0-
        (parameters.length:ℂ)⁻¹*axial.fullField bounded (radius.val,angles) 0-
        (radius.val:ℂ)⁻¹*retained.fullField bounded (radius.val,angles) 0
    have normalized : scalarDirectionalField pressure bounded 0 (1,0,0) (radius.val,angles)+
        (radius.val:ℂ)⁻¹*pressure.fullField bounded (radius.val,angles) 0+
        (parameters.length:ℂ)⁻¹*axial.fullField bounded (radius.val,angles) 0+
        (radius.val:ℂ)⁻¹*retained.fullField bounded (radius.val,angles) 0=0 := by
      simpa only [div_eq_mul_inv,mul_comm] using actual
    linear_combination normalized
  have coefficient := originalScalarRadial_doubleCoefficient pressure bounded radius.val interior slopes derivatives mode
  rw [funext pointwise,rhs.fullField_doubleCoefficient bounded radius.val radius.property mode] at coefficient
  have pCoefficient : pressure.physicalCurve 0 radius.val mode=originalPhysicalCoefficient (tuple.val 0) radius.val mode :=
    (pressure.fullField_coefficient bounded radius.val radius.property mode).symm
  have axialCoefficient : axial.physicalCurve 0 radius.val mode=(Complex.I*(mode.2:ℂ)) •
      (angularMeanFreeMultiplier mode • negativeTraceCoefficient _ 0 0
        (tupleBThreeTrace parameters parameters.length compact lower positive state tuple radius) mode) := by
    rw [originalProjectedAxial_coefficient,originalKernelSevenCurves_bThree]
  have retainedCoefficient : retained.physicalCurve 0 radius.val mode=(radius.val:ℂ) •
      negativeTraceCoefficient _ 0 0 (tupleVTrace parameters parameters.length compact lower positive state tuple radius) mode := by
    rw [← retained.fullField_doubleCoefficient bounded radius.val radius.property mode,
      ← originalCurveNegativeTrace_coefficient retained bounded radius mode,originalKernelSevenCurves_lowPhysical,
      tuplePhysicalRowTrace_rV,negativeTraceCoefficient_smul]
  dsimp only [rhs] at coefficient
  rw [physicalCurve_sub,physicalCurve_sub,physicalCurve_smul,physicalCurve_smul,physicalCurve_smul] at coefficient
  change -(radius.val:ℂ)⁻¹ • pressure.physicalCurve 0 radius.val mode-
    (parameters.length:ℂ)⁻¹ • axial.physicalCurve 0 radius.val mode-
    (radius.val:ℂ)⁻¹ • retained.physicalCurve 0 radius.val mode=slopes mode at coefficient
  rw [pCoefficient,axialCoefficient,retainedCoefficient,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (positive.trans_le radius.property.1).ne')] at coefficient
  change slopes mode+(radius.val:ℂ)⁻¹ • originalPhysicalCoefficient (tuple.val 0) radius.val mode+
    (parameters.length:ℂ)⁻¹ • ((Complex.I*(mode.2:ℂ)) • (angularMeanFreeMultiplier mode • negativeTraceCoefficient _ 0 0
      (tupleBThreeTrace parameters parameters.length compact lower positive state tuple radius) mode))+
    negativeTraceCoefficient _ 0 0 (tupleVTrace parameters parameters.length compact lower positive state tuple radius) mode=0
  rw [← coefficient]
  module

end Grad.OriginalKernelHomogeneousGraph
