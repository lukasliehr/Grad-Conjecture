import AKBX4OriginalForwardInjectivityAndSecondLaw

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

/-- The accepted finite-jet correction plus a smooth realization of its
SAME literal residual solves the original source. Its solution is unique. -/
theorem actualFiniteJet_sameResidual_uniqueSolution
    (source : OriginalFlatSource parameters parameters.length)
    (correction : stateSmoothRange parameters reference insideR)
    (realizesResidual : (forward correction).val=
      actualFiniteSourceResidual parameters parameters.length (seed 0) reference insideR seed insideS base currentLow source) :
    let lift := actualFiniteReferenceLift parameters parameters.length (seed 0) lengthPositive
      reference insideR seed insideS base currentLow source
    forward (lift+correction)=source.val ∧
      realChartKappa parameters reference insideR (lift+correction)=0 ∧
      ∀ solution : stateSmoothRange parameters reference insideR,
        forward solution=source.val → solution=lift+correction := by
  dsimp only
  have residual : forward correction=source.val-forward
      (actualFiniteReferenceLift parameters parameters.length (seed 0) lengthPositive
        reference insideR seed insideS base currentLow source) := by
    apply Subtype.ext
    rw [realizesResidual,actualFiniteSourceResidual_literal parameters parameters.length (seed 0) lengthPositive
      reference insideR seed insideS base currentLow axis source]
  have solved : forward
      (actualFiniteReferenceLift parameters parameters.length (seed 0) lengthPositive
        reference insideR seed insideS base currentLow source+correction)=source.val := by
    rw [map_add,residual]
    abel
  refine ⟨solved,?_,?_⟩
  · rw [←realExtraction_forward parameters.length lengthPositive reference insideR seed insideS base axis,solved]
    exact source.property
  · intro solution equation
    exact literalPhysicalSmoothForward_injective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall (equation.trans solved.symm)

/-- The second order of the inverse is an actual equality of the same
finite-lift plus residual realization with the original flat direction. -/
theorem actualFiniteJet_sameResidual_secondInverseLaw
    (direction : LinearMap.ker (realChartKappa parameters reference insideR))
    (correction : stateSmoothRange parameters reference insideR)
    (realizesResidual : (forward correction).val=
      actualFiniteSourceResidual parameters parameters.length (seed 0) reference insideR seed insideS base currentLow
        (realFlatForward parameters.length lengthPositive reference insideR seed insideS base axis direction)) :
    actualFiniteReferenceLift parameters parameters.length (seed 0) lengthPositive
      reference insideR seed insideS base currentLow
        (realFlatForward parameters.length lengthPositive reference insideR seed insideS base axis direction)+correction=direction.val := by
  have solved := actualFiniteJet_sameResidual_uniqueSolution parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall
    (realFlatForward parameters.length lengthPositive reference insideR seed insideS base axis direction) correction realizesResidual
  exact (solved.2.2 direction.val rfl).symm

end Grad.OriginalCurrentInverseUniqueness
