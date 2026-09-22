import AKB10ExactSameOriginalPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
namespace Grad.AnnularWeightedSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The SAME original inverse in phase-conjugated Hilbert coordinates. -/
def conjugatedSmoothResponsePairCurve (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let response := originalSmoothSourceResponse parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  let point := radialClamp lower bounded.le radius
  (conjugatedCoupledXSection parameters lower length positive bounded lengthPositive grade response point,
    conjugatedCoupledXiSection parameters lower length positive bounded lengthPositive grade response point)

theorem conjugatedSmoothResponsePairCurve_continuous (grade : ℕ) :
    Continuous (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) := by
  have allGrades := originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  exact ((conjugatedCoupledXSection_continuous parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive _ allGrades grade).prodMk
    (conjugatedCoupledXiSection_continuous parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive _ allGrades grade)).comp (radialClamp_continuous lower (lowerHalf.trans (by norm_num)))

/-- Literal coefficient equality on the entire original closed collar. -/
theorem conjugatedSmoothResponsePairCurve_physical (grade : ℕ) (mode : ℤ × ℤ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    hilbertPairCoefficient mode (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius) =
      Real.exp (radialPhase parameters radius mode.2) •
        hilbertPairCoefficient mode (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core grade radius) := by
  have allGrades := originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  have samePoint : (radialClamp lower (lowerHalf.trans (by norm_num)) radius).val = radius :=
    congrArg Subtype.val (radialClamp_eq lower (lowerHalf.trans (by norm_num)) radius inside)
  apply Prod.ext
  · change conjugatedCoupledXSection parameters lower length positive _ lengthPositive grade _ _ mode =
      Real.exp (radialPhase parameters radius mode.2) • sameCoupledPhysicalXSection parameters lower length positive _ lengthPositive grade _ _ mode
    rw [conjugatedCoupledXSection_physical parameters lower length positive _ lengthPositive _ allGrades,
      sameCoupledPhysicalXSection_coefficient parameters lower length positive _ lengthPositive _ allGrades, samePoint]
  · change conjugatedCoupledXiSection parameters lower length positive _ lengthPositive grade _ _ mode =
      Real.exp (radialPhase parameters radius mode.2) • sameCoupledPhysicalXiSection parameters lower length positive _ lengthPositive grade _ _ mode
    rw [conjugatedCoupledXiSection_physical parameters lower length positive _ lengthPositive _ allGrades,
      sameCoupledPhysicalXiSection_coefficient parameters lower length positive _ lengthPositive _ allGrades, samePoint]

end Grad.AnnularWeightedSmoothCore
