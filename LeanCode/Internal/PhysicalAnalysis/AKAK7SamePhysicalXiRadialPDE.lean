import AKAK6ActualXiRadialEquation

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

/-- Genuine radial Xi equation for the SAME original reconstructed scalar.
The literal full first row j and original force f occur exactly once. -/
theorem sharedPhysicalXi_radial (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
        1 (current,angles))
      ((sharedActualXiRadialRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades).meanFree.fullField
        (lowerHalf.trans_lt (by norm_num)) (radius,angles)) (Icc lower 1) radius := by
  let rhs := sharedActualXiRadialRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have identified (mode : ℤ × ℤ) :
      (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data response curves allGrades mode radius).2 =
        rhs.meanFree.physicalCurve 0 radius mode := by
    apply collarCurve_eq_of_ae lower (lowerHalf.trans_lt (by norm_num))
      (fun location => (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data response curves allGrades mode location).2)
      (fun location => rhs.meanFree.physicalCurve 0 location mode)
      (continuous_snd.comp (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data response curves allGrades mode).continuous).continuousOn
      ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
        (rhs.meanFree.physicalCurve_smooth (lowerHalf.trans_lt (by norm_num)) 0).continuousOn)
      (sharedActualXiRadialRHS_actual parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades mode) inside
  have derivative := generalShared_physicalField_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades 1 radius inside angles
  simp only [show (1 : Fin 2) ≠ 0 from by decide,if_false] at derivative
  have rhsSame : physicalCharacterSeries (fun mode =>
      (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data response curves allGrades mode radius).2) angles =
        rhs.meanFree.fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) := by
    rw [fullField_scalarSeries rhs.meanFree (lowerHalf.trans_lt (by norm_num)) radius inside angles]
    exact congrArg (fun coefficients => physicalCharacterSeries coefficients angles) (funext identified)
  rw [rhsSame] at derivative
  exact derivative

end Grad.ActualPolarEquations
