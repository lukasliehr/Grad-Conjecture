import AKBR10SameActualOuterCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Cor18 Grad.PhysicalCoordinates
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularOriginalSmoothCore Grad.OriginalKernelCovariantRecovery Grad.ActualSmoothPhysicalField

variable (parameters : PhaseParameters) (compact : ℝ)
    (state : RetainedInverseState parameters parameters.length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))

include insideSeed constrained

/-- The original smooth-domain constraint kills the exact BCT high
boundary covector acting on its own original covariant U. -/
theorem originalDomain_actualHighBoundary_zero :
    fullNegativeKernelAction parameters 0 0 (highAngularKernel parameters 1)
      (fullNegativeKernelAction parameters 0 0
        (actualBoundaryMultiplier parameters parameters.length state.val.val.rho state.val.val.alpha state.val.val.delta
          state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.val.compactNonnegative
          state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall state.boundaryState.coefficientSmall)
        (originalCurveNegativeTrace
          (originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
            lower positive bounded vector) ⟨1,bounded.le,le_rfl⟩))=0 := by
  let curves := originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded vector
  let source : ℝ×ℝ→ComplexEuclidean 3 := fun angles => curves.fullField bounded (1,angles)
  have represents (mode : ℤ×ℤ) : negativeTraceCoefficient parameters 0 0
      (originalCurveNegativeTrace curves ⟨1,bounded.le,le_rfl⟩) mode=doubleCoefficient source mode := by
    have actual := originalCurveNegativeTrace_coefficient curves bounded ⟨1,bounded.le,le_rfl⟩ mode
    have phase : radialKernelParameters parameters (tupleRadius lower positive ⟨1,bounded.le,le_rfl⟩)=parameters := radialKernelParameters_one parameters
    rw [phase] at actual
    exact actual
  have sameProduct : originalBoundaryProduct parameters parameters.length compact state.boundaryState source=
      originalBoundaryRowSeries parameters
        (rowField parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector)) := by
    funext angles
    exact originalBoundaryProduct_sameOriginalRow parameters compact state lower positive bounded vector insideSeed angles
  apply NegativeTrace.ext_coefficient parameters 0 0
  intro mode
  rw [highAngularKernel_coefficient]
  have zeroCoefficient : negativeTraceCoefficient parameters 0 0 (0 : NegativeTrace parameters 0 0 1) mode=0 := by
    simp [negativeTraceCoefficient]
  rw [zeroCoefficient]
  by_cases high : 3≤|mode.1|
  · simp only [highAngularMultiplier,if_pos high,one_smul]
    have product := originalBoundaryMultiplier_coefficient parameters parameters.length compact state.boundaryState
      (originalCurveNegativeTrace curves ⟨1,bounded.le,le_rfl⟩) source
      (curves.fullField_continuous_angles bounded 1 ⟨bounded.le,le_rfl⟩) represents mode
    apply product.trans
    rw [sameProduct]
    exact originalDomain_boundaryRowCoefficient_zero parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      vector constrained mode (by omega)
  · simp only [highAngularMultiplier,if_neg high,zero_smul]

end Grad.OriginalKernelOuterUniqueness
