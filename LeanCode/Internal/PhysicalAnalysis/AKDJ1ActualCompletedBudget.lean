import AKDG4OneOriginalInverseRadius
import AKDC6ConstructedOriginalSmoothBranch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology ContDiff
namespace Grad.OriginalInverseNeighborhood
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.PhysicalCoordinates
open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCoreRealization
open Grad.ImplementationReadiness Grad.SmoothingFamily

/-- The actual physical budget on the original finite-grade ambient space. -/
def completedPhysicalBudget (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) (point : MixedAmbient parameters grade) : ℝ :=
  ‖(completedPhysicalMixedReferenceState parameters reference grade point).ofLp.2.ofLp.1 -
      fieldEmbed parameters 3 grade (planarReferenceCore parameters)‖ +
    |mixedSeed parameters grade point 0| + ‖(mixedJoint parameters grade point).ofLp.1‖

theorem completedPhysicalBudget_continuousOn (parameters : PhaseParameters) (reference : Seed.Parameters)
    (grade : ℕ) : ContinuousOn (completedPhysicalBudget parameters reference grade) (mixedDomain parameters grade) := by
  have fields := (completedPhysicalMixedReferenceState_contDiffOn parameters reference grade).continuousOn
  have first := ((WithLp.prodContinuousLinearEquiv 1 ℝ ℂ
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).continuous.comp_continuousOn fields).snd
  have second := ((WithLp.prodContinuousLinearEquiv 1 ℝ (AGrade parameters 3 grade)
    (AGrade parameters 1 grade)).continuous.comp_continuousOn first).fst
  have finite : Continuous (fun point : MixedAmbient parameters grade => mixedSeed parameters grade point 0) :=
    (continuous_apply 0).comp (mixedSeed parameters grade).continuous
  have curvature := ((WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).continuous.comp
    (mixedJoint parameters grade).continuous).fst
  exact ((second.sub continuousOn_const).norm.add finite.abs.continuousOn).add curvature.norm.continuousOn

/-- This continuous ambient budget is exactly the native physical B grade
of the original real chart, with no change of width or finite parameters. -/
theorem completedPhysicalBudget_core (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    completedPhysicalBudget parameters reference grade
      (mixedCoreEmbed parameters grade (seed,realJointCoreToJoint parameters reference insideR base)) =
    physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 grade := by
  unfold completedPhysicalBudget
  rw [completedPhysicalMixedReferenceState_core parameters reference insideR grade
    (seed,realJointCoreToJoint parameters reference insideR base) insideS axis,
    actualFiniteCurrentState_eq]
  change ‖fieldEmbed parameters 3 grade (planarReferenceCore parameters+
      actualFiniteCurrentField parameters reference insideR seed insideS base)-
      fieldEmbed parameters 3 grade (planarReferenceCore parameters)‖+|seed 0|+‖(base.1:ℂ)‖ = _
  rw [map_add,add_sub_cancel_left,fieldEmbed_norm,Complex.norm_real,Real.norm_eq_abs]
  rfl

end Grad.OriginalInverseNeighborhood
