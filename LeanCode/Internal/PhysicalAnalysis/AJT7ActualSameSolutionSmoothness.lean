import AJT6SameProjectedRadialBootstrap
import AJP7SameHighCoordinateDerivative
import AJS3SameLowCoordinateDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The accepted genuine high and low weak equations cover every nonzero
angular Fourier mode of the SAME original smooth-source inverse response. -/
theorem originalSmoothResponsePairCurve_nonzeroPDE (mode : ℤ × ℤ) (nonzero : mode.1 ≠ 0)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0 point))
      (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)) (Icc lower 1) radius := by
  by_cases high : 3 ≤ |mode.1|
  · have x := originalSmoothResponsePairCurve_high_derivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 1 ⟨mode,high⟩ radius inside
    have xi := originalSmoothResponsePairCurve_high_derivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 ⟨mode,high⟩ radius inside
    exact x.prodMk xi
  · have low : |mode.1| = 1 ∨ |mode.1| = 2 := by
      have strictlyPositive : 0 < |mode.1| := abs_pos.mpr nonzero
      omega
    have x := originalSmoothResponsePairCurve_low_derivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core (1,⟨mode,low⟩) radius inside
    have xi := originalSmoothResponsePairCurve_low_derivative parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core (0,⟨mode,low⟩) radius inside
    exact x.prodMk xi

/-- The actual SAME coupled inverse of every original smooth source is
radially C-infinity at EVERY polynomial Fourier grade on the original closed
positive collar, on the unchanged B8 ball and analytic widths. -/
theorem originalSmoothResponsePairCurve_smooth :
    ∀ grade, ContDiffOn ℝ ∞ (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) (Icc lower 1) :=
  originalSmoothResponsePairCurve_smooth_of_nonzeroPDE parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
    (originalSmoothResponsePairCurve_nonzeroPDE parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core)

theorem originalSmoothResponseXCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun radius => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius).1) (Icc lower 1) :=
  (ContinuousLinearMap.fst ℝ (CellL2 1) (CellL2 1)).contDiff.comp_contDiffOn
    (originalSmoothResponsePairCurve_smooth parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade)

theorem originalSmoothResponseXiCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun radius => (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius).2) (Icc lower 1) :=
  (ContinuousLinearMap.snd ℝ (CellL2 1) (CellL2 1)).contDiff.comp_contDiffOn
    (originalSmoothResponsePairCurve_smooth parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade)

/-- The all-grade derivative is in the full Hilbert norm and has the
original mean-free sector RHS, not merely modewise scalar derivatives. -/
theorem originalSmoothResponsePairCurve_hasDerivWithinAt (grade : ℕ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade)
      (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core grade radius) (Icc lower 1) radius := by
  have coordinate := originalMeanFreeSystem_allGradeDerivative parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
    (originalSmoothResponsePairCurve_nonzeroPDE parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core) grade
  exact hilbertPairDerivative_of_coordinates lower (lowerHalf.trans (by norm_num)) _ _
    (originalSmoothResponsePairCurve_continuous parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade).continuousOn
    (originalMeanFreeSystemRHS_continuousOn parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade)
    (fun mode point member => (coordinate mode point member).fst)
    (fun mode point member => (coordinate mode point member).snd) radius inside

end Grad.AnnularSmoothCore
