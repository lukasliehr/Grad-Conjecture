import AKCE1SameNativeOriginalBoundaryProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularStrongOrbit Grad.OriginalKernelOuterUniqueness

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower)
    (lowerHalf : lower≤1/2) (lengthPositive : 0<length)
    (candidate : CoupledSpace lower length positive lengthPositive)
    (graphs : HighKnownGraphHilbert parameters lower)

/-- The full outer packet retains the actual copied F0,RF0,F2 graph traces. -/
theorem originalFullOuterSeven_withSources :
    originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate graphs=
      sevenSlotTrace parameters 0 0 (originalOuterX parameters lower length positive lowerHalf lengthPositive candidate)
        (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate)
        (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp) := by
  rw [originalFullOuterSeven,lowOuterSevenTrace_apply]
  apply PiLp.ext
  intro slot
  change sevenSlotTrace parameters 0 0 _ _ _ slot+actualSevenSlotTrace parameters length 0 0 _ _ 0 slot=_
  simp only [congrFun (sevenSlotTrace_components parameters 0 0 _ _ _) slot,
    congrFun (actualSevenSlotTrace_components parameters length 0 0 _ _ 0) slot]
  fin_cases slot <;> simp [originalOuterX,originalOuterXi,map_add]

/-- All actual boundary coefficients, including both copied source graphs. -/
theorem originalFullOuterSeven_sourcedCoefficient (mode : ℤ×ℤ) (slot : Fin 7) :
    negativeTraceCoefficient parameters 0 0
      (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate graphs slot) mode=
      ![negativeTraceCoefficient parameters 0 0 (originalOuterX parameters lower length positive lowerHalf lengthPositive candidate) mode,
        (Complex.I*(mode.1:ℂ)) • positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode,
        (Complex.I*(mode.2:ℂ)) • positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode,
        positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode,
        negativeTraceCoefficient parameters 0 0 (sourceBoundaryToNegative parameters 0 0 (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp 0)) mode,
        negativeTraceCoefficient parameters 0 0 (sourceBoundaryToNegative parameters 0 0 (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp 1)) mode,
        negativeTraceCoefficient parameters 0 0 (sourceBoundaryToNegative parameters 0 0 (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 graphs.ofLp 2)) mode] slot := by
  rw [originalFullOuterSeven_withSources]
  fin_cases slot
  · rfl
  · exact positiveRotationToNegative_coefficient parameters 0 0 _ mode
  · exact positiveCellToNegative_coefficient parameters 0 0 _ mode
  · exact positiveToNegative_coefficient parameters 0 0 _ mode
  · rfl
  · rfl
  · rfl

end Grad.OriginalCoreRealization
