import AJT1ClosedCollarPairDerivative
import AJQ4ExactSmoothSourceSystemConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularCoupledInverse

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- Ambient continuous curve of the SAME inverse field. Its values on the
closed collar are the original full Hilbert sections at the requested grade. -/
def originalSmoothResponsePairCurve (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let response := originalSmoothSourceResponse parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  let point := radialClamp lower bounded.le radius
  (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade response point,
    sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade response point)

theorem originalSmoothResponsePairCurve_continuous (grade : ℕ) :
    Continuous (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) :=
  (originalSmoothSourceResponse_pair_continuous parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade).comp
    (radialClamp_continuous lower (lowerHalf.trans (by norm_num)))

/-- The complete original RHS in the two Hilbert coordinates. -/
def originalSmoothResponseSystemRHS (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  (originalRadialSystemOperator parameters length compact lower state positive bounded grade radius)
    (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core (grade + 2) radius) +
    originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius

theorem originalSmoothResponseSystemRHS_continuousOn (grade : ℕ) :
    ContinuousOn (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) (Icc lower 1) := by
  exact ((originalRadialSystemOperator_smooth parameters length compact lower state positive
    (lowerHalf.trans_lt (by norm_num)) grade).continuousOn.clm_apply
    (originalSmoothResponsePairCurve_continuous parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core (grade + 2)).continuousOn).add
      (originalRadialSystemSource_smooth parameters length compact lower positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade).continuousOn

/-- The globally continuous candidate required by the actual high and low
weak-to-strong consumers, agreeing with the complete RHS on the collar. -/
def originalSmoothResponseClampedRHS (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade
      (radialClamp lower (lowerHalf.trans (by norm_num)) radius)

theorem originalSmoothResponseClampedRHS_continuous (grade : ℕ) :
    Continuous (originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) :=
  continuous_clampedCurve lower (lowerHalf.trans (by norm_num)) _
    (originalSmoothResponseSystemRHS_continuousOn parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade)

theorem originalSmoothResponseClampedRHS_same (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius =
    originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius := by
  unfold originalSmoothResponseClampedRHS
  rw [radialClamp_eq lower (lowerHalf.trans (by norm_num)) radius inside]

end Grad.AnnularSmoothCore
