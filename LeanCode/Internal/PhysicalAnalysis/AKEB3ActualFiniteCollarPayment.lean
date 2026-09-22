import AKEB2ActualResidualCollarPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections

/-- Literal finite reference state and original flat source specialization,
with the uniform constant selected before every finite datum. -/
theorem actualFiniteSourceResidual_collar_payment (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
      (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain) (base : RealJointCore parameters reference insideR)
      (rho : ℝ)
      (low : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 6≤
        originalCubicLowRadius parameters length),
      physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 24≤1 →
      ∀ source : OriginalFlatSource parameters length,
      ‖quotientEta parameters (grade+10) (actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source)‖+
        (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 (grade+16))*
          ‖quotientEta parameters 9 (actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source)‖≤
      constant*(‖quotientEta parameters (grade+24) source.val.val‖+
        (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 (grade+24))*
          ‖quotientEta parameters 24 source.val.val‖) := by
  obtain ⟨constant,constant0,bound⟩ := originalRealFiniteLiftResidual_collar_payment parameters length grade
  refine ⟨constant,constant0,?_⟩
  intro reference insideR seed insideS base rho low bounded source
  exact bound rho base.1 (actualFiniteCurrentField parameters reference insideR seed insideS base) low bounded
    (actualFiniteCurrentScalar parameters reference insideR seed insideS base) source.val.val

end Grad.FinitePhysicalJetLift
