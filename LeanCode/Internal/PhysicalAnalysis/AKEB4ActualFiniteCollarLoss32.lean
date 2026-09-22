import AKEB3ActualFiniteCollarPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections

/-- Fixed loss32, including eight ranks of collar conversion, with the
original source base and state neighborhood independent of the high order. -/
theorem actualFiniteSourceResidual_collar_payment32 (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
      (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain) (base : RealJointCore parameters reference insideR)
      (rho : ℝ)
      (low : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 6≤
        originalCubicLowRadius parameters length),
      physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 24≤1 →
      ∀ source : OriginalFlatSource parameters length, ∀ total : ℕ, total≤grade+8 →
      ‖quotientEta parameters (total+10) (actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source)‖+
        (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 (total+16))*
          ‖quotientEta parameters 9 (actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source)‖≤
      constant*(‖quotientEta parameters (grade+32) source.val.val‖+
        (1+physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base) rho base.1 (grade+32))*
          ‖quotientEta parameters 32 source.val.val‖) := by
  obtain ⟨constant,constant0,bound⟩ := actualFiniteSourceResidual_collar_payment parameters length (grade+8)
  refine ⟨constant,constant0,?_⟩
  intro reference insideR seed insideS base rho low bounded source total allocated
  let field := actualFiniteCurrentField parameters reference insideR seed insideS base
  let residual := actualFiniteSourceResidual parameters length rho reference insideR seed insideS base low source
  have actual := bound reference insideR seed insideS base rho low bounded source
  have top : grade+8+24=grade+32 := by omega
  simp only [top] at actual
  have first : ‖quotientEta parameters (total+10) residual‖+
      (1+physicalBudget parameters field rho base.1 (total+16))*‖quotientEta parameters 9 residual‖≤
      ‖quotientEta parameters (grade+8+10) residual‖+
        (1+physicalBudget parameters field rho base.1 (grade+8+16))*‖quotientEta parameters 9 residual‖ := by
    exact add_le_add (originalSourceNorm_monotone parameters residual (by omega))
      (mul_le_mul_of_nonneg_right (add_le_add (le_refl _) (physicalBudget_monotone parameters field rho base.1 (by omega))) (norm_nonneg _))
  apply (first.trans actual).trans
  apply mul_le_mul_of_nonneg_left ?_ constant0
  apply add_le_add (le_refl _)
  exact mul_le_mul_of_nonneg_left (originalSourceNorm_monotone parameters source.val.val (by norm_num : 24≤32))
    (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _))

end Grad.FinitePhysicalJetLift
