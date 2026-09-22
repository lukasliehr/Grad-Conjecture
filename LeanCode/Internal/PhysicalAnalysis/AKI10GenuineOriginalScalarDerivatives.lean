import AKI9SameOriginalPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongOrbit Grad.AnnularPhysicalFourier Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- Derivatives of the actual physical coefficients come from the accepted
original weak PDE, upgraded in the SAME Hilbert curve. -/
theorem originalPhysicalXi_derivWithin (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    derivWithin (fun location => originalPhysicalCoefficient
      (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      location mode) (Icc lower 1) radius =
      (if mode.1 = 0 then (0 : ℂ) else 1) •
        (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 radius)).2 := by
  have pair := ((hilbertPairCoefficient mode).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt radius
    (originalSmoothResponsePairCurve_hasDerivWithinAt parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius inside)
  have derivative : HasDerivWithinAt (fun location => (hilbertPairCoefficient mode
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 location)).2)
    (hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)).2
    (Icc lower 1) radius := pair.snd
  have same : ∀ location ∈ Icc lower 1, originalPhysicalCoefficient
      (originalSmoothResponsePhysicalXi parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      location mode = (hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core 0 location)).2 := by
    intro location member
    exact originalSmoothResponsePhysicalXi_coefficient parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core location member mode
  have actual := derivative.congr same (same radius inside)
  rw [actual.derivWithin ((uniqueDiffOn_Icc (lowerHalf.trans_lt (by norm_num))).uniqueDiffWithinAt inside)]
  exact congrArg Prod.snd (physicalPairMeanFree_coefficient parameters mode
    (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core 0 radius))

theorem originalPhysicalP_derivWithin (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    derivWithin (fun location => originalPhysicalCoefficient
      (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      location mode) (Icc lower 1) radius =
      angularInverseMultiplier mode • ((if mode.1 = 0 then (0 : ℂ) else 1) •
        (hilbertPairCoefficient mode (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 radius)).1) := by
  have pair := ((hilbertPairCoefficient mode).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt radius
    (originalSmoothResponsePairCurve_hasDerivWithinAt parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius inside)
  have first : HasDerivWithinAt (fun location => (hilbertPairCoefficient mode
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 location)).1)
    (hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)).1
    (Icc lower 1) radius := pair.fst
  have derivative : HasDerivWithinAt (fun location => angularInverseMultiplier mode • (hilbertPairCoefficient mode
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 location)).1)
    (angularInverseMultiplier mode • (hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 radius)).1)
    (Icc lower 1) radius := first.const_smul (angularInverseMultiplier mode)
  have same : ∀ location ∈ Icc lower 1, originalPhysicalCoefficient
      (originalSmoothResponsePhysicalP parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      location mode = angularInverseMultiplier mode • (hilbertPairCoefficient mode
        (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core 0 location)).1 := by
    intro location member
    exact (originalSmoothResponsePhysicalP_coefficient parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core location member mode).trans (physicalAngularPrimitive_apply parameters _ mode)
  have actual := derivative.congr same (same radius inside)
  rw [actual.derivWithin ((uniqueDiffOn_Icc (lowerHalf.trans_lt (by norm_num))).uniqueDiffWithinAt inside)]
  exact congrArg (fun value => angularInverseMultiplier mode • value)
    (congrArg Prod.fst (physicalPairMeanFree_coefficient parameters mode
      (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core 0 radius)))

end Grad.AnnularOriginalSmoothCore
