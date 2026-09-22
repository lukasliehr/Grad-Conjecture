import AJI15SameCoupledContinuousFields
import AJF40FiniteSourceActualGraphGrade
import AJE57SameReconstructedSmoothSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open Set
namespace Grad.AnnularSmoothCore
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The original SAME smooth-source solution, without a regularity premise. -/
def originalSmoothSourceResponse : CoupledSpace lower length positive lengthPositive :=
  sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core)

/-- Genuine finite support of every original source coordinate supplies all
inserted graph grades of the SAME coupled inverse output. -/
theorem originalSmoothSourceResponse_allGrades (grade : ℕ) :
    ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) weighted := by
  obtain ⟨weighted, same, _⟩ := finiteSharedResponse_insertedGrade parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core)
    (originalSmoothSupport parameters core)
    (strongSmoothDenseMap_supported parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive core) grade
  exact ⟨weighted, same⟩

/-- Continuous original physical (x,xi) at every polynomial Fourier grade on
the closed positive collar. No solution smoothness is claimed here. -/
theorem originalSmoothSourceResponse_pair_continuous (grade : ℕ) :
    Continuous (fun radius : Icc lower (1 : ℝ) =>
      (sameCoupledPhysicalXSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive grade
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) radius,
       sameCoupledPhysicalXiSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive grade
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) radius)) :=
  (sameCoupledPhysicalXSection_continuous parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) grade).prodMk
  (sameCoupledPhysicalXiSection_continuous parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) grade)

end Grad.AnnularSmoothCore
