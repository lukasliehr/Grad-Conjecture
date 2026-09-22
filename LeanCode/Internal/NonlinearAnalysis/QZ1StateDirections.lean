import QY5FixedGrades

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.SmoothForward

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges
open Grad.Q24Realization Grad.ConstrainedGrades

theorem forwardLarge {grade : ℕ} (large : 4 ≤ grade) : 3 ≤ grade := by omega

/-- Insert a state direction with zero curvature variation, retaining the
literal state norm. Finite seed parameters are held fixed. -/
def stateDirection (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    stateRange parameters reference insideR grade large →L[ℝ]
      RealJointAmbient parameters reference insideR grade large :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
    (stateRange parameters reference insideR grade large)).symm.toContinuousLinearMap.comp
    ((0 : stateRange parameters reference insideR grade large →L[ℝ] ℝ).prod
      (ContinuousLinearMap.id ℝ (stateRange parameters reference insideR grade large)))

theorem stateDirection_norm (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (direction : stateRange parameters reference insideR grade large) :
    ‖stateDirection parameters reference insideR grade large direction‖ = ‖direction‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖(0 : ℝ)‖ + ‖direction‖ = ‖direction‖
  simp only [norm_zero, zero_add]

theorem stateDirection_core (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (direction : stateSmoothRange parameters reference insideR) :
    stateDirection parameters reference insideR grade large
      (stateSmoothEmbedding parameters reference insideR grade large direction) =
    realJointCoreEmbed parameters reference insideR grade large (0, direction) := rfl

theorem stateDirection_lowering {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (direction : stateRange parameters reference insideR upper (large.trans ordered)) :
    realJointLowering parameters reference insideR large ordered
      (stateDirection parameters reference insideR upper (large.trans ordered) direction) =
    stateDirection parameters reference insideR lower large
      (stateLowering parameters reference insideR large ordered direction) := rfl

theorem realJointCoreEmbed_norm (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (base : RealJointCore parameters reference insideR) :
    ‖realJointCoreEmbed parameters reference insideR grade large base‖ =
      |base.1| + ‖stateSmoothEmbedding parameters reference insideR grade large base.2‖ := by
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖base.1‖ + ‖stateSmoothEmbedding parameters reference insideR grade large base.2‖ = _
  rw [Real.norm_eq_abs]

theorem realJointLowering_core {lower upper : ℕ} (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (base : RealJointCore parameters reference insideR) :
    realJointLowering parameters reference insideR large ordered
      (realJointCoreEmbed parameters reference insideR upper (large.trans ordered) base) =
    realJointCoreEmbed parameters reference insideR lower large base := by
  change WithLp.toLp 1 (base.1, stateLowering parameters reference insideR large ordered
    (stateSmoothEmbedding parameters reference insideR upper (large.trans ordered) base.2)) = _
  rw [stateLowering_core]
  rfl

end Grad.SmoothForward
