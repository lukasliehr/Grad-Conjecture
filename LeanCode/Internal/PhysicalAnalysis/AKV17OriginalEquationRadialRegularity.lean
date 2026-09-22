import AKV16GeneralActualSourceRadialBootstrap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

/-- Generic regularity for an arbitrary solution of the actual original
coupled equation, with actual all-grade source curves and actual inserted
field grades. Uniqueness identifies it with the same accepted inverse. -/
theorem originalEquation_phaseWeighted_radial
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data))
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) weighted) :
    ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) grade)
      (Icc lower 1) := by
  let weightedData := originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data
  let field := originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate
  have same : field = sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData :=
    sharedStrongResponse_unique parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData field equation
  have responseGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData) weighted := by
    rw [← same]
    exact allGrades
  have smooth := generalShared_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData curves responseGrades
  rw [← same] at smooth
  exact smooth

end Grad.AnnularGeneralSourceRegularity
