import AKCE9SameFullNativeOuterTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lowerHalf : lower≤1/2) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

open Grad.OriginalKernelOuterUniqueness Grad.OriginalKernelCovariantRecovery Grad.BoundaryKernelAction

include allGrades smooth


variable (compact : ℝ) (state : RetainedInverseState parameters length compact)

/-- The normalized native polar covariant and the exact BCT outer covariant are the SAME completed action. -/
theorem originalNativeCovariant_outer :
    originalCurveNegativeTrace (seven.covariant parameters length compact lower positive bounded state.val) ⟨1,bounded.le,le_rfl⟩=
      fullNegativeKernelAction parameters 0 0 state.boundaryState.covariant
        (sevenSlotFlatten parameters 0 0
          (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive field
            (WithLp.toLp 2 (strongKnownGraphPair parameters lower positive bounded data)))) := by
  rw [originalFullOuterSeven_sameNative parameters lower length positive bounded lowerHalf lengthPositive data field allGrades smooth seven]
  unfold SmoothLowPhysicalRow.covariant
  apply (originalCurveNegativeTrace_action parameters lower positive bounded
    (fun radius => radialNormalizedCovariantKernel parameters length compact state.val.val radius state.val.property)
    (Grad.AnnularKernelContinuity.radialNormalizedCovariantKernel_regular parameters length compact state.val)
    (Grad.AnnularWeightedSmoothness.radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded)
    seven ⟨1,bounded.le,le_rfl⟩).trans
  exact originalSameKernel_action (radialKernelParameters_one parameters) _ _
    (radialNormalizedCovariantKernel_one parameters length compact state.val.val state.val.property) _

end Grad.OriginalCoreRealization
