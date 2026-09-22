import Q24FixedSeedMap
import QU3AmbientCompatibility

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.Constraints
open Grad.AxisCore Grad.SmoothingFamily Grad.ConstrainedGrades Grad.CompatibleCompletion

theorem chartCoreEmbed_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (chartCoreEmbed parameters grade) := by
  let inner := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm
  let outer := (WithLp.prodContinuousLinearEquiv 1 ℝ (AxisGrade parameters 2 (grade + 1))
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm
  have innerDense := inner.surjective.denseRange.comp
    ((fieldEmbed_denseRange parameters 3 grade).prodMap
      (fieldEmbed_denseRange parameters 1 grade)) inner.continuous
  exact outer.surjective.denseRange.comp
    ((tangentToGrade_denseRange parameters (grade + 1)).prodMap innerDense) outer.continuous

theorem jointCoreEmbed_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (jointCoreEmbed parameters grade) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).symm.surjective.denseRange.comp
    (denseRange_id.prodMap (chartCoreEmbed_denseRange parameters grade))
    (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters grade)).symm.continuous

theorem xLowering_chartCore {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : ChartState parameters) :
    xLowering parameters ordered (chartCoreEmbed parameters upper state) =
      chartCoreEmbed parameters lower state := by
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · exact axisLowering_tangent parameters (Nat.add_le_add_right ordered 1) state.1
  · apply (WithLp.equiv 1 _).injective
    exact Prod.ext (completedInclusion_apply_eta parameters ordered (GradeCore.ofCoreLinear state.2.1))
      (completedInclusion_apply_eta parameters ordered (GradeCore.ofCoreLinear state.2.2))

def jointLowering {lower upper : ℕ} (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    JointAmbient parameters upper →L[ℝ] JointAmbient parameters lower :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters lower)).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℝ ℂ).prodMap ((xLowering parameters ordered).restrictScalars ℝ)).comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ ℂ (XAmbient parameters upper)).toContinuousLinearMap)

theorem jointLowering_core {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : JointState parameters) :
    jointLowering parameters ordered (jointCoreEmbed parameters upper state) =
      jointCoreEmbed parameters lower state := by
  change WithLp.toLp 1 (state.1, xLowering parameters ordered (chartCoreEmbed parameters upper state.2)) = _
  rw [xLowering_chartCore]
  rfl

theorem jointLowering_norm_le {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : JointAmbient parameters upper) :
    ‖jointLowering parameters ordered state‖ ≤ ‖state‖ := by
  rw [WithLp.prod_norm_eq_of_L1 (jointLowering parameters ordered state),
    WithLp.prod_norm_eq_of_L1 state]
  change ‖state.ofLp.1‖ + ‖xLowering parameters ordered state.ofLp.2‖ ≤
    ‖state.ofLp.1‖ + ‖state.ofLp.2‖
  exact add_le_add le_rfl (xLowering_norm_le parameters ordered state.ofLp.2)

theorem jointLowering_domain_iff {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (state : JointAmbient parameters upper) :
    jointLowering parameters ordered state ∈ jointDomain parameters lower ↔
      state ∈ jointDomain parameters upper := by
  change ‖axisLowering parameters (show 1 ≤ lower + 1 by omega)
    (axisLowering parameters (Nat.add_le_add_right ordered 1) state.ofLp.2.ofLp.1)‖ < _ ↔ _
  rw [axisLowering_trans]
  rfl

end Grad.Q24Realization
