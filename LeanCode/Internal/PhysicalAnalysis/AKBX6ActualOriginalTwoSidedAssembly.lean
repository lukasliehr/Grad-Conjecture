import AKBX5SameFiniteJetResidualInverseAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
namespace Grad.OriginalCurrentInverseUniqueness
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.FinitePhysicalJetLift Grad.OriginalKernelCovariantRecovery Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ActualPuncturedFamily
open Grad.ChartAxisProjections Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds

variable (parameters : PhaseParameters) (compact : ℝ)
  (lengthPositive : 0<parameters.length) (widthHalf : parameters.gamma≤1/2)
  (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
  (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
  (base : RealJointCore parameters reference insideR)
  (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
  (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (seed 0) base.1 8≤actualJetExhaustionRadius parameters parameters.length compact)
  (compactNonnegative : 0≤compact) (alphaSmall : |seed 1|≤compact)
  (deltaSmall : |seed 2|≤compact) (parameterSmall : |seed 3|≤compact)

include axis lengthPositive widthHalf widthLength small compactNonnegative alphaSmall deltaSmall parameterSmall

local notation "currentLow" => actualJetExhaustion_cubicSmall parameters parameters.length compact reference insideR seed insideS base small
local notation "forward" => literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis

/-- Reuse the existing original axis/flat coordinates to assemble the full
source. The only open input is the smooth realization of the SAME actual
finite-jet residual; both inverse orders then follow on the original domain. -/
theorem actualFiniteJet_fullOriginalSource_twoSided
    (radius : ℝ) (radiusPositive : 0<radius) (radiusBounded : radius≤1)
    (source : sourceSmoothRange parameters)
    (correction : stateSmoothRange parameters reference insideR)
    (realizesResidual : (forward correction).val=
      actualFiniteSourceResidual parameters parameters.length (seed 0) reference insideR seed insideS base currentLow
        ((realRangeCoordinates radius radiusPositive radiusBounded parameters.length lengthPositive
          reference insideR seed insideS base axis) source).2) :
    let data := (realRangeCoordinates radius radiusPositive radiusBounded parameters.length lengthPositive
      reference insideR seed insideS base axis) source
    let corrected := actualFiniteReferenceLift parameters parameters.length (seed 0) lengthPositive
      reference insideR seed insideS base currentLow data.2+correction
    ∃ flatProof : realChartKappa parameters reference insideR corrected=0,
      let reconstructed := (realDomainCoordinates radius radiusPositive radiusBounded
        reference insideR seed insideS base axis).symm (data.1,⟨corrected,flatProof⟩)
      forward reconstructed=source ∧
        ∀ direction : stateSmoothRange parameters reference insideR,
          forward direction=source → reconstructed=direction := by
  dsimp only
  let data := (realRangeCoordinates radius radiusPositive radiusBounded parameters.length lengthPositive
    reference insideR seed insideS base axis) source
  let corrected := actualFiniteReferenceLift parameters parameters.length (seed 0) lengthPositive
    reference insideR seed insideS base currentLow data.2+correction
  have flatSolved := actualFiniteJet_sameResidual_uniqueSolution parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall data.2 correction realizesResidual
  refine ⟨flatSolved.2.1,?_,?_⟩
  · apply (realRangeCoordinates radius radiusPositive radiusBounded parameters.length lengthPositive
      reference insideR seed insideS base axis).injective
    rw [realForward_coordinates radius radiusPositive radiusBounded parameters.length lengthPositive]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact flatSolved.1
  · intro direction equation
    apply literalPhysicalSmoothForward_injective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall
    rw [equation]
    apply (realRangeCoordinates radius radiusPositive radiusBounded parameters.length lengthPositive
      reference insideR seed insideS base axis).injective
    rw [realForward_coordinates radius radiusPositive radiusBounded parameters.length lengthPositive]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact flatSolved.1

end Grad.OriginalCurrentInverseUniqueness
