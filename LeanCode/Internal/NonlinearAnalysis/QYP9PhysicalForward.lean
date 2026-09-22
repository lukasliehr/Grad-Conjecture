import QYP8PhysicalPublicContract
import QY33ForwardCompatibility

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward

theorem realMixedAtSeed_contDiff (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (seed : Seed.Parameters) :
    ContDiff ℝ ∞ (realMixedAtSeed parameters reference insideR grade large seed) := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR grade large) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR grade large) := inferInstance
  exact (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference insideR grade large)).symm.contDiff.comp
      (contDiff_const.prodMk contDiff_id)

/-- Fix the literal seed in the corrected physical mixed residual. -/
def completedRealPhysicalFixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) :
    sourceRange parameters grade large :=
  completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large
    (realMixedAtSeed parameters reference insideR (grade + 6) (realHighLarge grade) seed state)

theorem completedRealPhysicalFixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    ContDiffOn ℝ ∞ (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed grade large)
      (realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :=
  (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference insideR grade large).comp
    (realMixedAtSeed_contDiff parameters reference insideR _ _ seed).contDiffOn
    (realMixedAtSeed_mem parameters reference insideR _ _ seed insideS)

theorem completedRealPhysicalFixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    sourceInclusion parameters grade large
      (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed grade large
        (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) base)) =
    quotientEta parameters grade (physicalFixedSliceMap parameters cellLength reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR base)) :=
  completedRealPhysicalMixedSlice_core parameters cellLength reference insideR grade large (seed, base) insideS axis

theorem completedRealPhysicalFixedSlice_fderiv (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    fderiv ℝ (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed grade large) state =
    (fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
      (realMixedAtSeed parameters reference insideR (grade + 6) (realHighLarge grade) seed state)).comp
      (realMixedJointDirection parameters reference insideR (grade + 6) (realHighLarge grade)) := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  have mixedInside := realMixedAtSeed_mem parameters reference insideR _ _ seed insideS state inside
  have smooth := (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference insideR grade large).contDiffAt
    ((realMixedDomain_isOpen parameters reference insideR _ _).mem_nhds mixedInside)
  exact ((smooth.differentiableAt (by simp)).hasFDerivAt.comp state
    (realMixedAtSeed_hasFDerivAt parameters reference insideR _ _ seed state)).fderiv

/-- The actual physical state derivative, with seed and curvature fixed,
on the exact original constrained carriers and six-grade loss. -/
def actualPhysicalSmoothForward (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (grade : ℕ) (large : 4 ≤ grade)
    (base : RealJointCore parameters reference insideR) :
    stateRange parameters reference insideR (grade + 6) (realHighLarge grade) →L[ℝ]
      sourceRange parameters grade (forwardLarge large) :=
  (fderiv ℝ (completedRealPhysicalFixedSlice parameters cellLength reference insideR seed grade (forwardLarge large))
    (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) base)).comp
    (stateDirection parameters reference insideR (grade + 6) (realHighLarge grade))

theorem actualPhysicalSmoothForward_mixed (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base =
    ((fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade (forwardLarge large))
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) (seed, base))).comp
      (realMixedJointDirection parameters reference insideR (grade + 6) (realHighLarge grade))).comp
      (stateDirection parameters reference insideR (grade + 6) (realHighLarge grade)) := by
  unfold actualPhysicalSmoothForward
  rw [completedRealPhysicalFixedSlice_fderiv parameters cellLength reference insideR seed insideS grade
    (forwardLarge large) _ ((realJointDomain_core_iff parameters reference insideR _ _ base).2 axis)]
  rfl

end Grad.PhysicalCoordinates
