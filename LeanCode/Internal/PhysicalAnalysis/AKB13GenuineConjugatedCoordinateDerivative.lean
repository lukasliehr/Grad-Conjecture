import AKB12FiniteReserveBootstrap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- Genuine product derivative of the SAME phase-conjugated inverse. The
phase slope is the original curved phase, and the RHS is the accepted actual
full system including all sources and the original mean-free projection. -/
theorem conjugatedSmoothResponsePairCurve_coordinateDerivative (grade : ℕ) (mode : ℤ × ℤ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => hilbertPairCoefficient mode (conjugatedSmoothResponsePairCurve parameters length compact lower
        positive lowerHalf lengthPositive widthHalf widthLength state small core grade point))
      (Real.exp (radialPhase parameters radius mode.2) •
        (annularPhaseSlope parameters mode.2 radius •
          hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
            lengthPositive widthHalf widthLength state small core grade radius) +
          hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf
            lengthPositive widthHalf widthLength state small core grade radius)))
      (Icc lower 1) radius := by
  have physical := originalMeanFreeSystem_allGradeDerivative parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
    (originalSmoothResponsePairCurve_nonzeroPDE parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core) grade mode radius inside
  have phase := (radialPhase_hasDerivAt parameters mode.2 radius).exp.hasDerivWithinAt (s := Icc lower 1)
  have product := phase.smul physical
  have equality := conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade mode
  have same := product.congr equality (equality radius inside)
  simpa only [smul_add, smul_smul, Function.comp_apply, add_comm] using same

end Grad.AnnularWeightedSmoothCore
