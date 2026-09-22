import QY7MixedGrades
import QZ6Consumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ContDiff Topology

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.QuotientProjection
open Grad.NonlinearQuotientBounds Grad.SmoothForward

private theorem affine_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (linear : E →L[ℝ] F) (offset : F) (point : E) :
    HasFDerivAt (fun input => offset + linear input) linear point :=
  linear.hasFDerivAt.const_add offset

private theorem fixed_parameter_derivative {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (insertion : E → F) (linear : E →L[ℝ] F) (mapping : F → G) (fixed : E → G)
    (point : E) (insertionDerivative : HasFDerivAt insertion linear point)
    (smooth : ContDiffAt ℝ ∞ mapping (insertion point))
    (agreement : (fun input => mapping (insertion input)) =ᶠ[𝓝 point] fixed) :
    (fderiv ℝ mapping (insertion point)).comp linear = fderiv ℝ fixed point := by
  have derivative := (smooth.differentiableAt (by simp)).hasFDerivAt.comp point insertionDerivative
  exact (derivative.congr_of_eventuallyEq agreement.symm).fderiv.symm

/-- A joint direction in the mixed carrier with exactly zero seed variation. -/
def realMixedJointDirection (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    RealJointAmbient parameters reference insideR grade large →L[ℝ]
      RealMixedAmbient parameters reference insideR grade large :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference insideR grade large)).symm.toContinuousLinearMap.comp
    ((0 : RealJointAmbient parameters reference insideR grade large →L[ℝ] SeedL1).prod
      (ContinuousLinearMap.id ℝ (RealJointAmbient parameters reference insideR grade large)))

/-- Fix the seed without modifying the joint state. -/
def realMixedAtSeed (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (seed : Seed.Parameters) (state : RealJointAmbient parameters reference insideR grade large) :
    RealMixedAmbient parameters reference insideR grade large :=
  WithLp.toLp 1 (WithLp.toLp 1 seed, state)

theorem realMixedAtSeed_hasFDerivAt (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (seed : Seed.Parameters) (state : RealJointAmbient parameters reference insideR grade large) :
    HasFDerivAt (realMixedAtSeed parameters reference insideR grade large seed)
      (realMixedJointDirection parameters reference insideR grade large) state := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR grade large) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR grade large) := inferInstance
  have same : realMixedAtSeed parameters reference insideR grade large seed =
      fun point => WithLp.toLp 1 (WithLp.toLp 1 seed,
        (0 : RealJointAmbient parameters reference insideR grade large)) +
        realMixedJointDirection parameters reference insideR grade large point := by
    funext point
    change WithLp.toLp 1 (WithLp.toLp 1 seed, point) =
      WithLp.toLp 1 (WithLp.toLp 1 seed + 0, 0 + point)
    simp only [add_zero, zero_add]
  rw [same]
  exact affine_derivative _ _ state

theorem realMixedAtSeed_mem (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : RealJointAmbient parameters reference insideR grade large)
    (inside : state ∈ realJointDomain parameters reference insideR grade large) :
    realMixedAtSeed parameters reference insideR grade large seed state ∈
      realMixedDomain parameters reference insideR grade large :=
  ⟨insideS, inside⟩

theorem completedRealMixedSlice_fixedSeed (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    completedRealMixedSlice parameters cellLength reference insideR grade large
      (realMixedAtSeed parameters reference insideR (grade + 6) (realHighLarge grade) seed state) =
    completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large state := by
  apply Subtype.ext
  change sourceInclusion parameters grade large _ = sourceInclusion parameters grade large _
  rw [completedRealMixedSlice_inclusion parameters cellLength reference insideR grade large _
    (realMixedAtSeed_mem parameters reference insideR _ _ seed insideS state inside),
    completedRealFixedSlice_inclusion parameters cellLength reference insideR seed insideS grade large state inside]
  exact completedMixedSlice_agrees parameters cellLength reference insideR grade _ insideS

/-- Restricting the actual mixed derivative to zero seed variation gives
the actual fixed-seed derivative, on every completed admissible state. -/
theorem completedRealMixedSlice_fixedSeed_fderiv (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (state : RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade))
    (inside : state ∈ realJointDomain parameters reference insideR (grade + 6) (realHighLarge grade)) :
    (fderiv ℝ (completedRealMixedSlice parameters cellLength reference insideR grade large)
      (realMixedAtSeed parameters reference insideR (grade + 6) (realHighLarge grade) seed state)).comp
      (realMixedJointDirection parameters reference insideR (grade + 6) (realHighLarge grade)) =
    fderiv ℝ (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large) state := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade + 6) (realHighLarge grade)) := inferInstance
  have mixedInside := realMixedAtSeed_mem parameters reference insideR _ _ seed insideS state inside
  have mixedSmooth := (completedRealMixedSlice_contDiffOn parameters cellLength reference insideR grade large).contDiffAt
    ((realMixedDomain_isOpen parameters reference insideR _ _).mem_nhds mixedInside)
  have agreement : (fun point => completedRealMixedSlice parameters cellLength reference insideR grade large
      (realMixedAtSeed parameters reference insideR (grade + 6) (realHighLarge grade) seed point))
      =ᶠ[𝓝 state] completedRealFixedSlice parameters cellLength reference insideR seed insideS grade large := by
    filter_upwards [(realJointDomain_isOpen parameters reference insideR _ _).mem_nhds inside] with point member
    exact completedRealMixedSlice_fixedSeed parameters cellLength reference insideR seed insideS grade large point member
  exact fixed_parameter_derivative _ _ _ _ state
    (realMixedAtSeed_hasFDerivAt parameters reference insideR _ _ seed state) mixedSmooth agreement

/-- Immediate COR29 consumer: the mixed Q24 map differentiates to the
accepted literal forward operator in every pure state direction. -/
theorem completedRealMixedSlice_actualSmoothForward (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    ((fderiv ℝ (completedRealMixedSlice parameters cellLength reference insideR grade (forwardLarge large))
      (realMixedCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) (seed, base))).comp
      (realMixedJointDirection parameters reference insideR (grade + 6) (realHighLarge grade))).comp
      (stateDirection parameters reference insideR (grade + 6) (realHighLarge grade)) =
    actualSmoothForward parameters cellLength reference insideR seed insideS grade large base := by
  change ((fderiv ℝ _ (realMixedAtSeed parameters reference insideR _ _ seed
    (realJointCoreEmbed parameters reference insideR _ _ base))).comp _).comp _ = _
  rw [completedRealMixedSlice_fixedSeed_fderiv parameters cellLength reference insideR seed insideS
    grade (forwardLarge large) _
    ((realJointDomain_core_iff parameters reference insideR _ _ base).2 axis)]
  rfl

end Grad.Q24Realization
