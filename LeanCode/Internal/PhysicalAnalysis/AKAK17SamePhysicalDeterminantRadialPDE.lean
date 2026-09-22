import AKAK16ActualDeterminantSlopeRecovery
import AKAK10RadialEquationFourierUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)

variable
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

include curves allGrades

/-- Genuine classical determinant radial equation for the SAME original
x, c, rV and g fields, at every radius of the original closed collar. -/
theorem sharedPhysicalX_radial (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
        0 (current,angles))
      (determinantPhysicalRHS length radius
        (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
          seven third radius) angles) (Icc lower 1) radius := by
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let fields := actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius
  have regular := generalShared_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades
  have fieldSmooth := actualDeterminantFields_smooth parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius inside
  have angular := actualDeterminantFields_angular parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius
  have cell := actualDeterminantFields_cell parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius
  apply hilbertPhysicalField_radial_of_doubleCoefficients lower positive (lowerHalf.trans_lt (by norm_num))
    (originalPhysicalComponentCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive response 0)
    (originalPhysicalComponentCurve_smooth parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive response allGrades regular 0)
    (originalPhysicalComponentCurve_grade parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive response allGrades 0)
    radius inside
    (fun mode => (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data response curves allGrades mode radius).1)
    _ (determinantPhysicalRHS length radius fields)
    (determinantPhysicalRHS_continuous length radius fields fieldSmooth)
    (determinantPhysicalRHS_angular length radius fields angular)
    (determinantPhysicalRHS_cell length radius fields cell) _ angles
  · intro mode
    have derivative := generalShared_physical_derivative parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades mode radius inside
    exact (ContinuousLinearMap.fst ℝ (ComplexEuclidean 1) (ComplexEuclidean 1)).hasFDerivAt.comp_hasDerivWithinAt radius derivative
  · intro mode
    rw [determinantPhysicalRHS_coefficient length radius fields fieldSmooth angular cell]
    change determinantModeRHS length radius mode (fun index => Grad.SourceCollarFullSource.doubleCoefficient (fields index) mode) = _
    have represented (index : Fin 4) := actualDeterminantFields_coefficient parameters length compact lower positive lowerHalf lengthPositive
      state data response seven third radius inside index mode
    exact (congrArg (determinantModeRHS length radius mode) (funext represented)).trans
      (actualDeterminantSlope_pointwise parameters length compact lower positive lowerHalf lengthPositive state data response seven third curves allGrades radius inside mode).symm

end Grad.ActualPolarEquations
