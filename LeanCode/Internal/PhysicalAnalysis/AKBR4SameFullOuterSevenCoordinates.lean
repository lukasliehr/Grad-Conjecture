import AKBR3SameFullOuterRetainedTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularStrongOrbit

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower)
    (lowerHalf : lower≤1/2) (lengthPositive : 0<length)
    (candidate : CoupledSpace lower length positive lengthPositive)

/-- With the actual copied graphs zero, the original full seven boundary
uses exactly the full high-plus-low x and Xi traces. -/
theorem originalFullOuterSeven_zeroSources :
    originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate 0=
      sevenSlotTrace parameters 0 0 (originalOuterX parameters lower length positive lowerHalf lengthPositive candidate)
        (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) 0 := by
  have graphs : highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0
      (0 : HighKnownGraphHilbert parameters lower).ofLp=0 := by
    rw [← highGraphOuterTupleMap_apply,map_zero]
  rw [originalFullOuterSeven,graphs,lowOuterSevenTrace_apply]
  apply PiLp.ext
  intro slot
  change sevenSlotTrace parameters 0 0 _ _ 0 slot+actualSevenSlotTrace parameters length 0 0 _ _ 0 slot=_
  simp only [congrFun (sevenSlotTrace_components parameters 0 0 _ _ 0) slot,
    congrFun (actualSevenSlotTrace_components parameters length 0 0 _ _ 0) slot]
  fin_cases slot <;> simp [originalOuterX,originalOuterXi,map_add]

/-- All seven Fourier slots, in the original unscaled r=1 convention. -/
theorem originalFullOuterSeven_coefficient (mode : ℤ×ℤ) (slot : Fin 7) :
    negativeTraceCoefficient parameters 0 0
      (originalFullOuterSeven parameters length lower positive lowerHalf lengthPositive candidate 0 slot) mode=
      ![negativeTraceCoefficient parameters 0 0 (originalOuterX parameters lower length positive lowerHalf lengthPositive candidate) mode,
        (Complex.I*(mode.1:ℂ)) • positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode,
        (Complex.I*(mode.2:ℂ)) • positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode,
        positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode,
        0,0,0] slot := by
  rw [originalFullOuterSeven_zeroSources]
  fin_cases slot
  · rfl
  · exact positiveRotationToNegative_coefficient parameters 0 0 _ mode
  · exact positiveCellToNegative_coefficient parameters 0 0 _ mode
  · exact positiveToNegative_coefficient parameters 0 0 _ mode
  · simp [sevenSlotTrace,negativeTraceCoefficient]
  · simp [sevenSlotTrace,negativeTraceCoefficient]
  · simp [sevenSlotTrace,negativeTraceCoefficient]

end Grad.OriginalKernelOuterUniqueness
