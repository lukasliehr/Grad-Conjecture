import AKCE8ClosedKnownSevenCoefficients

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

/-- The full sourced outer seven trace is precisely the SAME native curve's negative trace.
This includes the genuine copied graph endpoint coordinates, not homogeneous substitutes. -/
theorem originalFullOuterSeven_sameNative :
    sevenSlotFlatten parameters 0 0
      (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive field
        (WithLp.toLp 2 (strongKnownGraphPair parameters lower positive bounded data)))=
      originalCurveNegativeTrace seven ⟨1,bounded.le,le_rfl⟩ := by
  have represents (mode : ℤ×ℤ) : negativeTraceCoefficient parameters 0 0
      (originalCurveNegativeTrace seven ⟨1,bounded.le,le_rfl⟩) mode=seven.physicalCurve 0 1 mode := by
    have exactCurve := originalCurveNegativeTrace_coefficient seven bounded ⟨1,bounded.le,le_rfl⟩ mode
    have phase : radialKernelParameters parameters (Grad.AnnularOriginalSmoothCore.tupleRadius lower positive ⟨1,bounded.le,le_rfl⟩)=parameters :=
      radialKernelParameters_one parameters
    rw [phase] at exactCurve
    exact exactCurve.trans (seven.fullField_doubleCoefficient bounded 1 ⟨bounded.le,le_rfl⟩ mode)
  apply NegativeTrace.ext_coefficient parameters 0 0
  intro mode
  rw [represents mode]
  apply PiLp.ext
  intro slot
  rw [sevenSlotFlatten_coefficient,originalFullOuterSeven_sourcedCoefficient]
  rw [originalOuterX_physical,originalOuterXi_physical]
  have first (index : Fin 4) := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (fullSeven_firstFour_closed parameters lower length positive bounded lengthPositive data field allGrades smooth seven 1
      ⟨bounded.le,le_rfl⟩ mode index)
  have known (index : Fin 3) := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (fullSeven_known_outer parameters lower length positive bounded lengthPositive data field seven mode index)
  fin_cases slot
  · simpa [matrixUnit_apply,operatorBasis] using (first 0).symm
  · simpa [matrixUnit_apply,operatorBasis,frequencyNumerator] using (first 1).symm
  · simpa [matrixUnit_apply,operatorBasis,frequencyNumerator] using (first 2).symm
  · simpa [matrixUnit_apply,operatorBasis] using (first 3).symm
  · simpa [sourceBoundaryToNegative_coefficient,matrixUnit_apply,operatorBasis] using (known 0).symm
  · simpa [sourceBoundaryToNegative_coefficient,matrixUnit_apply,operatorBasis] using (known 1).symm
  · simpa [sourceBoundaryToNegative_coefficient,matrixUnit_apply,operatorBasis] using (known 2).symm

end Grad.OriginalCoreRealization
