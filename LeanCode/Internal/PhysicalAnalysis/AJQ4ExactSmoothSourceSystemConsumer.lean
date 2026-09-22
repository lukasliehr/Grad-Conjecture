import AJQ2ActualKnownSourceRHS
import AJQ3SameSmoothSourceContinuousSolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularCoupledInverse
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation

/-- Exact source/initial-regularity boundary for the actual radial bootstrap:
one original smooth datum, literal decoded source RHS, and the SAME weak solve. -/
theorem originalSmoothSourceSystem_consumer
    (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters) (grade : ℕ) :
    let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
    let source := originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade
    let response := originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core
    ContDiffOn ℝ ∞ source (Icc lower 1) ∧
    (∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      ((source radius).1 mode, (source radius).2 mode) =
        ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
          actualOriginalSourceRHS parameters length compact lower positive bounded lengthPositive state core radius mode) ∧
    Continuous (fun radius : Icc lower (1 : ℝ) =>
      (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade response radius,
       sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade response radius)) := by
  exact ⟨originalRadialSystemSource_smooth parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade,
    originalRadialSystemSource_actual parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade,
    originalSmoothSourceResponse_pair_continuous parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core grade⟩

end Grad.AnnularSmoothCore
