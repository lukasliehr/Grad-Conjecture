import AKCE2OriginalPhysicalRowConverse
import AKCE10SameActualOuterCovariant
import AKCE11SourcedOuterCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
open scoped ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularStrongOrbit Grad.OriginalKernelOuterUniqueness Grad.AnnularSmoothCore
open Grad.ActualSmoothPhysicalField Grad.OriginalKernelCovariantRecovery Grad.Constraints Grad.Cor18 Grad.PhysicalCoordinates
open Grad.AnnularHighGenerators
open Grad.AnnularWeightedSmoothCore Grad.OriginalKernelRetainedDecay
open Grad.AnnularGeneralSourceRegularity Grad.AnnularPhysicalFourier Grad.SourceCollarFullSource

variable (parameters : PhaseParameters) (compact lower : ℝ) (positive : 0<lower) (lowerHalf : lower≤1/2)
    (lengthPositive : 0<parameters.length) (state : RetainedInverseState parameters parameters.length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower parameters.length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower parameters.length positive lengthPositive,
      CoupledInsertedGrade lower parameters.length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower parameters.length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field grade) (Icc lower 1))
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters parameters.length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field))
    (vector : ACore parameters 3)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (same : ∀ angles : ℝ×ℝ,
      ((seven.covariant parameters parameters.length compact lower positive (lowerHalf.trans_lt (by norm_num)) state.val).physicalUFromPolar
        parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low lower positive
        (lowerHalf.trans_lt (by norm_num))).fullField (lowerHalf.trans_lt (by norm_num)) (1,angles)=
          originalCoreCircle parameters vector ⟨1,zero_le_one,le_rfl⟩ angles)
    (outer : coupledFullOuterBoundary parameters parameters.length compact lower positive lowerHalf lengthPositive state field
      (WithLp.toLp 2 (strongKnownGraphPair parameters lower positive (lowerHalf.trans_lt (by norm_num)) data))=0)

include allGrades smooth same outer

/-- The actual full sourced outer equation enforces precisely the original physical row
on the SAME recovered vector. No copied source graph is discarded. -/
theorem nativeOuter_originalPhysicalRow :
    physicalRow parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector)=0 := by
  let bounded : lower<1 := lowerHalf.trans_lt (by norm_num)
  let graphs := WithLp.toLp 2 (strongKnownGraphPair parameters lower positive bounded data)
  let input := originalFullOuterSeven parameters parameters.length lower positive lowerHalf lengthPositive field graphs
  have zeroPR : lowStateBoundaryPR parameters parameters.length compact state input=0 :=
    (originalFullOuterSeven_boundary parameters parameters.length compact lower positive lowerHalf lengthPositive state field graphs).symm.trans outer
  have supported := originalFullOuterSeven_supported parameters lower parameters.length positive lowerHalf lengthPositive field graphs
  have derivative := originalFullOuterSeven_scalarDerivative parameters lower parameters.length positive lowerHalf lengthPositive field graphs
  have primitive := actualPhysicalBoundaryPR_eq_high parameters parameters.length state.boundaryState.val.rho state.boundaryState.val.alpha
    state.boundaryState.val.delta state.boundaryState.val.parameter state.boundaryState.val.epsilon compact state.boundaryState.val.field
    state.boundaryState.property state.boundaryState.val.compactNonnegative state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall
    state.boundaryState.val.parameterSmall 0 0 input supported derivative
  have high : actualHighPhysicalBoundary parameters parameters.length state.boundaryState.val.rho state.boundaryState.val.alpha
    state.boundaryState.val.delta state.boundaryState.val.parameter state.boundaryState.val.epsilon compact state.boundaryState.val.field
    state.boundaryState.property state.boundaryState.val.compactNonnegative state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall
    state.boundaryState.val.parameterSmall 0 0 input=0 := by
    apply primitive.symm.trans
    change highBoundaryPrimitiveTrace parameters 0 0 (lowStateBoundaryPR parameters parameters.length compact state input)=0
    rw [zeroPR]
    simp [highBoundaryPrimitiveTrace]
  unfold actualHighPhysicalBoundary fullSevenSlotKernelAction actualHighPhysicalBoundaryKernel at high
  simp only [ContinuousLinearMap.comp_apply,fullNegativeKernelAction_comp] at high
  change fullNegativeKernelAction parameters 0 0 (highAngularKernel parameters 1)
    (fullNegativeKernelAction parameters 0 0
      (actualBoundaryMultiplier parameters parameters.length state.val.val.rho state.val.val.alpha state.val.val.delta state.val.val.parameter
        state.val.val.epsilon compact state.val.val.field state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall
        state.val.val.parameterSmall state.boundaryState.coefficientSmall)
      (fullNegativeKernelAction parameters 0 0 state.boundaryState.covariant (sevenSlotFlatten parameters 0 0 input)))=0 at high
  have covariant := originalNativeCovariant_outer parameters lower parameters.length positive bounded lowerHalf lengthPositive data field
    allGrades smooth seven compact state
  change originalCurveNegativeTrace (seven.covariant parameters parameters.length compact lower positive bounded state.val) ⟨1,bounded.le,le_rfl⟩=
    fullNegativeKernelAction parameters 0 0 state.boundaryState.covariant (sevenSlotFlatten parameters 0 0 input) at covariant
  rw [← covariant] at high
  exact originalPhysicalRow_zero_of_nativeBoundary parameters compact state lower positive bounded vector insideSeed
    (seven.covariant parameters parameters.length compact lower positive bounded state.val) same high

end Grad.OriginalCoreRealization
