import AKU88ActualRealLinearFlatLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections

/-- The same real linear lift on the original flat source has the original
flat smooth domain and the literal original higher-vanishing residual. -/
theorem actualFiniteFlatLiftLinear_reduces (parameters : PhaseParameters) (length rho : ℝ) (positive : 0 < length)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (low : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 6 ≤
      originalCubicLowRadius parameters length) (source : OriginalFlatSource parameters length) :
    let lift := actualFiniteFlatLiftLinear parameters length rho positive reference insideR seed insideS base low source
    let residual := source.val - literalPhysicalSmoothForward parameters length reference insideR seed insideS base axis lift.val
    IsFlat residual.val ∧ SourceHigherVanishing residual.val ∧
      residual.val = actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source := by
  dsimp only
  rw [actualFiniteFlatLiftLinear_apply]
  rw [← actualFiniteSourceResidual_literal parameters length rho positive reference insideR seed insideS base low axis source]
  exact ⟨actualFiniteSourceResidual_isFlat parameters length rho positive reference insideR seed insideS base low axis source,
    actualFiniteSourceResidual_higherVanishing parameters length rho positive reference insideR seed insideS base low axis source,rfl⟩

end Grad.FinitePhysicalJetLift
