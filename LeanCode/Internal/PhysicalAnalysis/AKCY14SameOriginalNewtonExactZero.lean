import AKCY13OriginalStageUniformLimits

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Filter
open scoped Topology

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.NashMoser.Numeric
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates

/-- Actual real mixed completed state fiber, with the same finite inputs. -/
def realStateFiber (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (finite : OriginalFiniteParameter) (state : stateRange parameters reference inside grade large) :
    RealMixedAmbient parameters reference inside grade large :=
  WithLp.toLp 1 (WithLp.toLp 1 finite.1,WithLp.toLp 1 (finite.2,state))

theorem realStateFiber_continuous (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (finite : OriginalFiniteParameter) : Continuous (realStateFiber parameters reference inside grade large finite) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference inside grade large)).symm.continuous.comp
      (continuous_const.prodMk ((WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
        (stateRange parameters reference inside grade large)).symm.continuous.comp
          (continuous_const.prodMk continuous_id)))

theorem realStateFiber_core (parameters : PhaseParameters) (reference : Seed.Parameters)
    (inside : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference inside) :
    realStateFiber parameters reference inside grade large finite
      (stateSmoothEmbedding parameters reference inside grade large state) =
    realMixedCoreEmbed parameters reference inside grade large (finite.1,finite.2,state) := rfl

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

namespace OriginalNewtonScale
variable (scale : OriginalNewtonScale inverse)

theorem originalLimit_axis (point : scale.parameterDomain) :
    ChartAxisCondition (smoothingChartCore parameters (scale.originalLimit point).val) :=
  neighborhood.axis _ (((stateSize_mono parameters reference inside base (Nat.zero_le loss) _).trans
    (scale.originalLimit_low point)).trans (by linarith [neighborhood.radiusPositive]))

theorem residual_tendsto_zero (point : scale.parameterDomain) :
    Tendsto (fun index => sourceSmoothEmbedding parameters (base+loss) (by have := neighborhood.baseLarge; omega)
      (inverse.residual point.val (scale.iterate point.val point.property index))) atTop
      (𝓝 (0 : sourceRange parameters (base+loss) (by have := neighborhood.baseLarge; omega))) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (scale.iterate_decay point.val point.property)
    (newtonTime_decay_tendsto scale.initialLarge (by unfold initialDecay; nlinarith [Nat.cast_nonneg (α := ℝ) loss]))

/-- The reconstructed SAME original smooth core solves the literal nonlinear
source equation exactly. Actual QYP continuity, not a zero-limit premise,
is applied at the original source grade and its six-grade state input. -/
theorem originalLimit_exact_zero (point : scale.parameterDomain) :
    originalNonlinearSource parameters cellLength reference inside point.val (scale.originalLimit point) = 0 := by
  let grade := base+loss
  have large : 3 ≤ grade := by dsimp [grade]; have := neighborhood.baseLarge; omega
  have seed := neighborhood.patchInside (neighborhood.seedInside point.val point.property.1)
  let candidate := realMixedCoreEmbed parameters reference inside (grade+6) (realHighLarge grade)
    (point.val.1,point.val.2,scale.originalLimit point)
  have domain : candidate ∈ realMixedDomain parameters reference inside (grade+6) (realHighLarge grade) :=
    (realMixedDomain_core_iff parameters reference inside (grade+6) (realHighLarge grade)
      (point.val.1,point.val.2,scale.originalLimit point)).2 ⟨seed,scale.originalLimit_axis point⟩
  have mixedConverges := ((realStateFiber_continuous parameters reference inside (grade+6) (realHighLarge grade)
    point.val).tendsto (stateSmoothEmbedding parameters reference inside (grade+6) (realHighLarge grade)
      (scale.originalLimit point))).comp (scale.originalLimit_tendsto point ⟨grade+6,realHighLarge grade⟩)
  simp only [Function.comp_def,realStateFiber_core] at mixedConverges
  have continuous := (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference inside grade large).continuousOn.continuousAt
    ((realMixedDomain_isOpen parameters reference inside (grade+6) (realHighLarge grade)).mem_nhds domain)
  have mapped := continuous.tendsto.comp mixedConverges
  have realization (index : ℕ) :
      completedRealPhysicalMixedSlice parameters cellLength reference inside grade large
        (realMixedCoreEmbed parameters reference inside (grade+6) (realHighLarge grade)
          (point.val.1,point.val.2,scale.iterate point.val point.property index)) =
      sourceSmoothEmbedding parameters grade large (inverse.residual point.val (scale.iterate point.val point.property index)) :=
    (originalNonlinearSource_completed parameters cellLength reference inside point.val
      (scale.iterate point.val point.property index) seed
      (neighborhood.axis _ (((stateSize_mono parameters reference inside base (Nat.zero_le loss) _).trans
        (scale.iterate_low point.val point.property index)).trans (by linarith [neighborhood.radiusPositive]))) grade large).symm
  simp only [Function.comp_def,realization] at mapped
  apply sourceSmoothEmbedding_injective parameters grade large
  rw [map_zero,originalNonlinearSource_completed parameters cellLength reference inside point.val
    (scale.originalLimit point) seed (scale.originalLimit_axis point)]
  exact tendsto_nhds_unique mapped (scale.residual_tendsto_zero point)

theorem iterate_zero_branch (point : scale.parameterDomain)
    (seedZero : originalNonlinearSource parameters cellLength reference inside point.val 0 = 0) (index : ℕ) :
    scale.iterate point.val point.property index = 0 := by
  induction index with
  | zero => exact scale.iterate_zero point.val point.property
  | succ index inductionHypothesis =>
    rw [scale.iterate_step,inductionHypothesis]
    simp only [OriginalNewtonInverse.correction,smoothedNewtonCorrection,OriginalNewtonInverse.residual,
      seedZero,map_zero]
    exact _root_.add_neg_cancel (0 : stateSmoothRange parameters reference inside)

theorem originalLimit_zero_branch (point : scale.parameterDomain)
    (seedZero : originalNonlinearSource parameters cellLength reference inside point.val 0 = 0) :
    scale.originalLimit point = 0 := by
  apply stateSmoothEmbedding_injective parameters reference inside 3 (le_refl 3)
  rw [map_zero]
  have converges := scale.originalLimit_tendsto point ⟨3,le_refl 3⟩
  simp only [scale.iterate_zero_branch point seedZero,map_zero] at converges
  exact tendsto_nhds_unique converges tendsto_const_nhds

end OriginalNewtonScale
end Grad.NashMoser.OriginalIteration
