import AKCE1SameNativeOriginalBoundaryProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.SourceCollar Grad.Cor18
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.OriginalKernelRetainedDecay Grad.AnnularReconstruction Grad.PhysicalCoordinates
open Grad.OriginalKernelCovariantRecovery Grad.ActualBoundaryPrimitives Grad.ActualPolarFlux
open Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Ledger

open Grad.OriginalKernelOuterUniqueness Grad.BoundaryKernelAction

variable (parameters : PhaseParameters) (compact : ℝ)
    (state : RetainedInverseState parameters parameters.length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (same : ∀ angles : ℝ×ℝ,
      (curves.physicalUFromPolar parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
        state.val.val.low lower positive bounded).fullField bounded (1,angles)=
          originalCoreCircle parameters vector ⟨1,zero_le_one,le_rfl⟩ angles)

include same

/-- The exact completed high boundary operator recovers the original physical row constraint
for any SAME recovered core; copied source terms remain inside the native covariant. -/
theorem originalPhysicalRow_zero_of_nativeBoundary
    (boundary : fullNegativeKernelAction parameters 0 0 (highAngularKernel parameters 1)
      (fullNegativeKernelAction parameters 0 0
        (actualBoundaryMultiplier parameters parameters.length state.val.val.rho state.val.val.alpha state.val.val.delta
          state.val.val.parameter state.val.val.epsilon compact state.val.val.field state.val.val.compactNonnegative
          state.val.val.alphaSmall state.val.val.deltaSmall state.val.val.parameterSmall state.boundaryState.coefficientSmall)
        (originalCurveNegativeTrace curves ⟨1,bounded.le,le_rfl⟩))=0) :
    physicalRow parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector)=0 := by
  let source : ℝ×ℝ→ComplexEuclidean 3 := fun angles => curves.fullField bounded (1,angles)
  have represents (mode : ℤ×ℤ) : negativeTraceCoefficient parameters 0 0
      (originalCurveNegativeTrace curves ⟨1,bounded.le,le_rfl⟩) mode=doubleCoefficient source mode := by
    have actual := originalCurveNegativeTrace_coefficient curves bounded ⟨1,bounded.le,le_rfl⟩ mode
    have phase : radialKernelParameters parameters (Grad.AnnularOriginalSmoothCore.tupleRadius lower positive ⟨1,bounded.le,le_rfl⟩)=parameters :=
      radialKernelParameters_one parameters
    rw [phase] at actual
    exact actual
  have sameProduct : originalBoundaryProduct parameters parameters.length compact state.boundaryState source=
      originalBoundaryRowSeries parameters
        (rowField parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector)) := by
    funext angles
    exact nativeBoundaryProduct_sameOriginalRow parameters compact state lower positive bounded vector insideSeed curves same angles
  apply Subtype.ext
  funext mode
  change physicalRowFamily parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
    (toPhysicalCore parameters vector) mode=0
  by_cases low : |mode.1|≤2
  · simp only [physicalRowFamily,if_pos low]
  · have high : 3≤|mode.1| := by omega
    rw [physicalRowFamily,if_neg low]
    have zero := congrArg (fun field : NegativeTrace parameters 0 0 1 => negativeTraceCoefficient parameters 0 0 field mode) boundary
    rw [highAngularKernel_coefficient] at zero
    simp only [highAngularMultiplier,if_pos high,one_smul] at zero
    have product := originalBoundaryMultiplier_coefficient parameters parameters.length compact state.boundaryState
      (originalCurveNegativeTrace curves ⟨1,bounded.le,le_rfl⟩) source
      (curves.fullField_continuous_angles bounded 1 ⟨bounded.le,le_rfl⟩) represents mode
    have result : doubleCoefficient (originalBoundaryProduct parameters parameters.length compact state.boundaryState source) mode=0 :=
      product.symm.trans (zero.trans (by simp [negativeTraceCoefficient]))
    rw [sameProduct,originalBoundaryRowSeries_coefficient] at result
    exact result

end Grad.OriginalCoreRealization
