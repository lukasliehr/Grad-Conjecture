import AKAF11SamePointwiseThirdForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualPolarEquations
open Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularRestriction Grad.AnnularPhysicalReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularHighGenerators
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion Grad.AnnularCoupledInverse
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation

variable
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤
      originalCoefficientLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (point : OriginalFiveBlockAmbient parameters lower length positive)
    (member : point ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (sameSources : point.ofLp.2 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
        lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) weighted)

/-- Both actual full pointwise force equations and the genuine angular
covariant derivative are consequences of the SAME original observed source
solution. This consumer does not assume any physical PDE identity. -/
theorem actualObserved_pointwise_force_and_angular
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
    let curves := actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades
    let covariant := curves.covariant parameters length compact lower positive bounded state.val
    let rotated := curves.rotatedCovariant parameters length compact lower positive bounded state.val
    let firstForce := physicalForceCurves parameters length compact lower positive bounded state.val 0 covariant
    let thirdForce := physicalForceCurves parameters length compact lower positive bounded state.val 1 covariant
    (firstForce.fullField bounded (radius,polar,axial) +
      (curves.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial) -
      (rotated.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial) -
      (2 : ℂ) • (covariant.bulkUnit (0 : Fin 1) 0).fullField bounded (radius,polar,axial) =
      (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,polar,axial)) ∧
    ((rotated.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,polar,axial) +
      Grad.SourceCollarFullSource.removePolarMean (fun query => thirdForce.fullField bounded (radius,query)) (polar,axial) -
      (length : ℂ)⁻¹ • (curves.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,polar,axial) =
      (curves.bulkUnit (0 : Fin 1) 6).fullField bounded (radius,polar,axial)) ∧
    HasDerivAt (fun angle => covariant.fullField bounded (radius,angle,axial))
      (rotated.fullField bounded (radius,polar,axial)) polar := by
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let data := originalStrongWeightEquivalence parameters lower length positive bounded.le lengthPositive 0 0
    (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      coefficientSmall lower positive bounded 0 source flat)
  let solution := originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive point.ofLp.1
  let curves := actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades
  exact ⟨sharedFull_firstForce_pointwise parameters length compact lower positive bounded lengthPositive state.val data solution
      curves radius inside (polar,axial),
    sharedFull_thirdForce_pointwise parameters length compact lower positive bounded lengthPositive state.val data solution
      curves radius inside (polar,axial),
    sharedCovariant_classical_angular parameters length compact lower positive bounded lengthPositive state.val data solution
      curves radius inside polar axial⟩

end Grad.ActualPolarEquations
