import AJT3PolynomialCoordinateDerivative
import AJI31SameSmoothSourceRHSConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse

def hilbertPairCoefficient (mode : ℤ × ℤ) :
    PhysicalHilbertPair →L[ℂ] ComplexEuclidean 1 × ComplexEuclidean 1 :=
  let evaluation := lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode
  (evaluation.comp (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1))).prod
    (evaluation.comp (ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)))

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

theorem originalSmoothResponsePairCurve_coefficient_grade (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius) =
    ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core 0 radius) := by
  apply Prod.ext
  · exact sameCoupledPhysicalXSection_grade parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core)
      (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core) grade _ mode
  · exact sameCoupledPhysicalXiSection_grade parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core)
      (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core) grade _ mode

/-- The actual all-grade coordinate derivative follows from the genuine
grade-zero PDE of the SAME pair. No higher-grade solution is chosen anew. -/
theorem originalSmoothResponsePairCurve_allGradeDerivative
    (baseLaw : ∀ mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt
        (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
          positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
        (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower
          positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)) (Icc lower 1) radius)
    (grade : ℕ) (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core grade point))
      (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core grade radius)) (Icc lower 1) radius := by
  apply coordinateDerivative_of_grade lower (lowerHalf.trans_lt (by norm_num))
    (((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ))
    (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core grade point))
    (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
    (fun point => hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core grade point))
    (fun point => hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
  · exact fun point _ => originalSmoothResponsePairCurve_coefficient_grade parameters length compact lower
      positive lowerHalf lengthPositive widthHalf widthLength state small core grade point mode
  · exact (hilbertPairCoefficient mode).continuous.comp_continuousOn
      (originalSmoothResponseSystemRHS_continuousOn parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core grade)
  · exact (hilbertPairCoefficient mode).continuous.comp_continuousOn
      (originalSmoothResponseSystemRHS_continuousOn parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0)
  · filter_upwards [originalSmoothSourceRHS_coefficient_grade parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade] with point same
    exact same mode
  · exact baseLaw mode
  · exact inside

/-- The complete fixed-collar radial bootstrap, awaiting only the genuine
base Fourier PDE supplied by the high, low and zero sectors. -/
theorem originalSmoothResponsePairCurve_smooth_of_basePDE
    (baseLaw : ∀ mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt
        (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
          positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
        (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower
          positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)) (Icc lower 1) radius) :
    ∀ grade, ContDiffOn ℝ ∞ (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) (Icc lower 1) := by
  apply physicalPairScale_smooth_of_coordinates lower (lowerHalf.trans_lt (by norm_num))
    (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core)
    (originalRadialSystemSource parameters length compact lower positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive state core)
    (originalRadialSystemOperator parameters length compact lower state positive (lowerHalf.trans_lt (by norm_num)))
  · exact fun grade => (originalSmoothResponsePairCurve_continuous parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade).continuousOn
  · exact originalRadialSystemSource_smooth parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state core
  · exact originalRadialSystemOperator_smooth parameters length compact lower state positive
      (lowerHalf.trans_lt (by norm_num))
  · intro grade mode radius inside
    exact (originalSmoothResponsePairCurve_allGradeDerivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core baseLaw grade mode radius inside).fst
  · intro grade mode radius inside
    exact (originalSmoothResponsePairCurve_allGradeDerivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core baseLaw grade mode radius inside).snd

end Grad.AnnularSmoothCore
