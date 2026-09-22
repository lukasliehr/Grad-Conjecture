import AKCV11LocalOriginalTaylorBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
open Set
namespace Grad.NashMoser.OriginalLimit
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds

/-- The original finite-coordinate norm and the original state grade
control the SAME Q24 mixed norm, with an explicit finite-dimensional factor. -/
theorem originalMixedCoreEmbed_norm_bound
    (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (core : RealMixedCore parameters reference insideR) :
    ‖realMixedCoreEmbed parameters reference insideR grade large core‖ ≤
      (‖originalFiniteDirectionCompleted parameters reference insideR grade large‖+1) *
        (‖(core.1,core.2.1)‖+‖stateSmoothEmbedding parameters reference insideR grade large core.2.2‖) := by
  have split : core = originalFiniteDirection parameters reference insideR (core.1,core.2.1)+
      originalStateDirection parameters reference insideR core.2.2 := by
    change (core.1,core.2.1,core.2.2) = (core.1+0,core.2.1+0,0+core.2.2)
    simp only [add_zero,zero_add]
  have same : realMixedCoreEmbed parameters reference insideR grade large core =
      originalFiniteDirectionCompleted parameters reference insideR grade large (core.1,core.2.1)+
      physicalStateDirection parameters reference insideR grade large
        (stateSmoothEmbedding parameters reference insideR grade large core.2.2) := by
    rw [originalFiniteDirectionCompleted_core,physicalStateDirection_core]
    change originalMixedCoreEmbedding parameters reference insideR grade large core =
      originalMixedCoreEmbedding parameters reference insideR grade large
        (originalFiniteDirection parameters reference insideR (core.1,core.2.1))+
      originalMixedCoreEmbedding parameters reference insideR grade large
        (originalStateDirection parameters reference insideR core.2.2)
    rw [← map_add,← split]
  rw [same]
  have triangle := norm_add_le
    (originalFiniteDirectionCompleted parameters reference insideR grade large (core.1,core.2.1))
    (physicalStateDirection parameters reference insideR grade large
      (stateSmoothEmbedding parameters reference insideR grade large core.2.2))
  rw [physicalStateDirection_norm] at triangle
  have finiteBound := (originalFiniteDirectionCompleted parameters reference insideR grade large).le_opNorm (core.1,core.2.1)
  nlinarith [norm_nonneg (core.1,core.2.1), norm_nonneg (stateSmoothEmbedding parameters reference insideR grade large core.2.2),
    mul_nonneg (norm_nonneg (originalFiniteDirectionCompleted parameters reference insideR grade large))
      (norm_nonneg (stateSmoothEmbedding parameters reference insideR grade large core.2.2))]

/-- Difference and lowering identities retain exactly the original finite
parameters and the grade-four state difference. -/
theorem originalMixedCoreEmbed_difference
    (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (base point : RealMixedCore parameters reference insideR) :
    realMixedCoreEmbed parameters reference insideR grade large point-
      realMixedCoreEmbed parameters reference insideR grade large base =
    realMixedCoreEmbed parameters reference insideR grade large (point-base) :=
  (originalMixedCoreEmbedding parameters reference insideR grade large).map_sub point base |>.symm


theorem originalMixedCoreEmbed_lowering
    (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    {lower upper : ℕ} (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (core : RealMixedCore parameters reference insideR) :
    realMixedLowering parameters reference insideR large ordered
      (realMixedCoreEmbed parameters reference insideR upper (large.trans ordered) core) =
    realMixedCoreEmbed parameters reference insideR lower large core := by
  change WithLp.toLp 1 (WithLp.toLp 1 core.1, WithLp.toLp 1 (core.2.1,
    stateLowering parameters reference insideR large ordered
      (stateSmoothEmbedding parameters reference insideR upper (large.trans ordered) core.2.2))) = _
  rw [stateLowering_core]
  rfl

end Grad.NashMoser.OriginalLimit
