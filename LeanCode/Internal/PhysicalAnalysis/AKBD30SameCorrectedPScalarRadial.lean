import AKBD29PrimitiveRadialSlopeFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.AnnularForwardDatum Grad.AnnularRestriction

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1/2) (state : RetainedInverseState parameters length compact)

variable (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

/-- Genuine vector-valued corrected-p differentiation yields exactly the
scalar derivative used in the determinant cancellation. -/
theorem sameCorrectedP_scalarRadial_of_classical (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ)
    (radialLaw : HasDerivWithinAt
      (fun location => (curves.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField
        (lowerHalf.trans_lt (by norm_num)) (location,angles))
      (primitiveDeterminantRHS length radius
        (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data solution curves third radius) angles)
      (Icc lower 1) radius) :
    scalarDirectionalField (curves.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state)
      (lowerHalf.trans_lt (by norm_num)) 0 (1,0,0) (radius,angles) =
      removePolarMean (fun query =>
        -(curves.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0 / (radius : ℂ) -
        scalarDirectionalField (curves.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state) (lowerHalf.trans_lt (by norm_num)) 0 (0,0,1) (radius,query) / (length : ℂ) -
        (curves.lowPhysicalCurves parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state 2).fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0 / (radius : ℂ) +
        third.fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0) angles := by
  have scalar := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius
    (radialLaw.hasDerivAt (Icc_mem_nhds inside.1 inside.2))
  have same := (scalarRadial_hasDerivAt (curves.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state)
    (lowerHalf.trans_lt (by norm_num)) 0 radius inside angles.1 angles.2).unique scalar
  exact same.trans (actualPrimitiveRHS_scalar parameters length compact lower positive lowerHalf state lengthPositive data solution curves third radius inside angles)

end Grad.ActualDeterminantEquations
