import AxisJetProfiles

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### The disk `L²` norm against a small support ball

The scaled profiles are supported in radius `1/(4 λ_n)`; the area of that
ball pays the `λ_n⁻¹` gain of M30. -/

/-- The square root of the unit closed-ball area of the plane. -/
def ballVolumeSqrt : ℝ :=
  Real.sqrt ((volume (Metric.closedBall (0 : SpatialPlane) 1)).toReal)

theorem ballVolumeSqrt_nonneg : 0 ≤ ballVolumeSqrt := Real.sqrt_nonneg _

/-- The restricted area of a small closed ball scales with its squared
radius. -/
theorem restricted_ball_measure_le (radius : ℝ) (radiusNonneg : 0 ≤ radius) :
    ((volume.restrict openUnitDisk)
        (Metric.closedBall (0 : SpatialPlane) radius)).toReal ≤
      radius ^ 2 * ballVolumeSqrt ^ 2 := by
  have finrankPlane : Module.finrank ℝ SpatialPlane = 2 := finrank_euclideanSpace_fin
  have scaled : volume (Metric.closedBall (0 : SpatialPlane) radius) =
      ENNReal.ofReal (radius ^ 2) * volume (Metric.closedBall (0 : SpatialPlane) 1) := by
    rw [MeasureTheory.Measure.addHaar_closedBall' volume 0 radiusNonneg, finrankPlane]
  have ballFinite : volume (Metric.closedBall (0 : SpatialPlane) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : SpatialPlane) 1).measure_lt_top.ne
  have restrictLe : (volume.restrict openUnitDisk)
      (Metric.closedBall (0 : SpatialPlane) radius) ≤
      volume (Metric.closedBall (0 : SpatialPlane) radius) := by
    rw [Measure.restrict_apply measurableSet_closedBall]
    exact measure_mono Set.inter_subset_left
  calc ((volume.restrict openUnitDisk)
      (Metric.closedBall (0 : SpatialPlane) radius)).toReal ≤
      (volume (Metric.closedBall (0 : SpatialPlane) radius)).toReal := by
        apply ENNReal.toReal_mono _ restrictLe
        rw [scaled]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ballFinite
    _ = radius ^ 2 * (volume (Metric.closedBall (0 : SpatialPlane) 1)).toReal := by
        rw [scaled, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg radius)]
    _ = radius ^ 2 * ballVolumeSqrt ^ 2 := by
        unfold ballVolumeSqrt
        rw [Real.sq_sqrt ENNReal.toReal_nonneg]

theorem sqrt_restricted_ball_le (radius : ℝ) (radiusNonneg : 0 ≤ radius) :
    Real.sqrt (((volume.restrict openUnitDisk)
        (Metric.closedBall (0 : SpatialPlane) radius)).toReal) ≤
      radius * ballVolumeSqrt := by
  have sqrtStep := Real.sqrt_le_sqrt (restricted_ball_measure_le radius radiusNonneg)
  rwa [show radius ^ 2 * ballVolumeSqrt ^ 2 = (radius * ballVolumeSqrt) ^ 2 from by ring,
    Real.sqrt_sq (mul_nonneg radiusNonneg ballVolumeSqrt_nonneg)] at sqrtStep

/-- The disk `L²` norm of a continuous closed field vanishing outside a
small closed ball costs only the small ball's area. -/
theorem l2_norm_le_sup_ball {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    {radius bound : ℝ} (radiusNonneg : 0 ≤ radius) (boundNonneg : 0 ≤ bound)
    (vanishing : ∀ point : ClosedDisk,
      point.val ∉ Metric.closedBall (0 : SpatialPlane) radius → field point = 0)
    (bounded : ∀ point : ClosedDisk, ‖field point‖ ≤ bound) :
    ‖closedContinuousToDiskL2 field‖ ≤ bound * (radius * ballVolumeSqrt) := by
  have squareBound : ‖closedContinuousToDiskL2 field‖ ^ 2 ≤
      bound ^ 2 * ((volume.restrict openUnitDisk)
        (Metric.closedBall (0 : SpatialPlane) radius)).toReal := by
    rw [closedContinuousToDiskL2_norm_sq]
    have fieldIntegrable : Integrable (fun point : SpatialPlane =>
        ‖closedDiskLift field point‖ ^ 2) (volume.restrict openUnitDisk) :=
      (memLp_two_iff_integrable_sq_norm (closedContinuous_memLp field).1).mp
        (closedContinuous_memLp field)
    have indicatorIntegrable : Integrable
        ((Metric.closedBall (0 : SpatialPlane) radius).indicator
          (fun _ => bound ^ 2)) (volume.restrict openUnitDisk) :=
      (integrable_const (bound ^ 2)).indicator measurableSet_closedBall
    have pointwise : ∀ᵐ point ∂volume.restrict openUnitDisk,
        ‖closedDiskLift field point‖ ^ 2 ≤
          (Metric.closedBall (0 : SpatialPlane) radius).indicator
            (fun _ => bound ^ 2) point := by
      filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet]
        with point membership
      have liftValue : closedDiskLift field point =
          field ⟨point, openDiskMembershipClosed point membership⟩ := by
        rw [closedDiskLift, dif_pos (openDiskMembershipClosed point membership)]
      by_cases inside : point ∈ Metric.closedBall (0 : SpatialPlane) radius
      · rw [Set.indicator_of_mem inside, liftValue]
        exact pow_le_pow_left₀ (norm_nonneg _) (bounded _) 2
      · rw [Set.indicator_of_notMem inside, liftValue,
          vanishing ⟨point, openDiskMembershipClosed point membership⟩ inside,
          norm_zero]
        norm_num
    calc (∫ point : SpatialPlane, ‖closedDiskLift field point‖ ^ 2
        ∂volume.restrict openUnitDisk) ≤
        ∫ point : SpatialPlane,
          (Metric.closedBall (0 : SpatialPlane) radius).indicator
            (fun _ => bound ^ 2) point ∂volume.restrict openUnitDisk :=
          integral_mono_ae fieldIntegrable indicatorIntegrable pointwise
      _ = ((volume.restrict openUnitDisk)
            (Metric.closedBall (0 : SpatialPlane) radius)).toReal • bound ^ 2 :=
          integral_indicator_const (bound ^ 2) measurableSet_closedBall
      _ = bound ^ 2 * ((volume.restrict openUnitDisk)
            (Metric.closedBall (0 : SpatialPlane) radius)).toReal := by
          rw [smul_eq_mul, mul_comm]
  have sqrtStep := Real.sqrt_le_sqrt squareBound
  rw [Real.sqrt_sq (norm_nonneg _)] at sqrtStep
  apply sqrtStep.trans
  rw [Real.sqrt_mul (sq_nonneg bound), Real.sqrt_sq boundNonneg]
  exact mul_le_mul_of_nonneg_left (sqrt_restricted_ball_le radius radiusNonneg)
    boundNonneg

/-! ### Uniform word constants for fixed compactly supported profiles -/

/-- Every finite order sits below the smooth exponent. -/
theorem natCast_le_infty (rank : ℕ) : ((rank : ℕ∞ω)) ≤ (∞ : ℕ∞ω) := by
  exact_mod_cast le_top

/-- Every derivative order of a fixed smooth compactly supported scalar has
one uniform supremum constant. -/
theorem compact_word_bound (profile : SpatialPlane → ℝ)
    (profileSmooth : ContDiff ℝ ∞ profile)
    (profileCompact : HasCompactSupport profile) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ point : SpatialPlane,
      ‖iteratedFDeriv ℝ order profile point‖ ≤ bound := by
  have derivativeContinuous :
      Continuous (fun point => ‖iteratedFDeriv ℝ order profile point‖) :=
    (profileSmooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have derivativeCompact :
      HasCompactSupport (fun point => ‖iteratedFDeriv ℝ order profile point‖) :=
    (profileCompact.iteratedFDeriv order).norm
  obtain ⟨top, topBound⟩ :=
    derivativeContinuous.exists_forall_ge_of_hasCompactSupport derivativeCompact
  exact ⟨‖iteratedFDeriv ℝ order profile top‖, norm_nonneg _, topBound⟩

/-- The operator-norm phase-weight word bound at every order, with the
uniform axis constants. -/
theorem weight_iterated_opnorm_bound (parameters : PhaseParameters) (cell : ℤ)
    (rank : ℕ) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point‖ ≤
      weightWordConstant parameters rank *
        Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ rank := by
  rcases Nat.eq_zero_or_pos rank with rankZero | rankPositive
  · subst rankZero
    rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
    rw [Real.norm_of_nonneg (cartesianWeight_pos parameters cell point).le]
    calc cartesianWeight parameters cell point ≤
        Real.exp (parameters.sigma0 * cellFrequency cell) :=
          cartesianWeight_le_exp parameters cell point
      _ = 1 * Real.exp (parameters.sigma0 * cellFrequency cell) := (one_mul _).symm
      _ ≤ weightWordConstant parameters 0 *
          Real.exp (parameters.sigma0 * cellFrequency cell) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have iteratedBound := Grad.AnalyticWeights.Higher.physicalWeight_iterated_norm_bound
      parameters.sigma0 parameters.gamma 1 cell parameters.gamma_pos.le zero_le_one
      rank rankPositive point
    have weightBound := cartesianWeight_le_exp parameters cell point
    calc ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point‖ ≤
        Grad.AnalyticWeights.Higher.partitionProductConstant rank *
          Grad.AnalyticWeights.Higher.weightCost rank parameters.gamma 1 *
          cartesianWeight parameters cell point *
          Grad.CellWeights.cellWeight cell ^ rank := iteratedBound
      _ ≤ weightWordConstant parameters rank *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ rank := by
          have stepOne : Grad.AnalyticWeights.Higher.partitionProductConstant rank *
              Grad.AnalyticWeights.Higher.weightCost rank parameters.gamma 1 *
              cartesianWeight parameters cell point ≤
              weightWordConstant parameters rank *
                Real.exp (parameters.sigma0 * cellFrequency cell) := by
            apply mul_le_mul (le_max_right _ _) weightBound
              (cartesianWeight_pos parameters cell point).le
              (weightWordConstant_nonneg parameters rank)
          apply mul_le_mul_of_nonneg_right stepOne
            (pow_nonneg (cellFrequency_pos cell).le rank)

/-! ### The word supremum of a scalar-profile times a constant vector -/

/-- The Cartesian derivative word of `y ↦ s(y) v` is controlled by the
operator norm of the scalar word times the vector norm. -/
theorem phased_word_norm {dimension : ℕ} (scalar : SpatialPlane → ℝ)
    (scalarSmooth : ContDiff ℝ ∞ scalar) (vector : ComplexEuclidean dimension)
    (order : ℕ) (word : CartesianWord order) (point : SpatialPlane) :
    ‖cartesianDerivative order word (fun target => scalar target • vector) point‖ ≤
      ‖iteratedFDeriv ℝ order scalar point‖ * ‖vector‖ := by
  have applied : cartesianDerivative order word
      (fun target => scalar target • vector) point =
      (iteratedFDeriv ℝ order scalar point
        (fun position => spatialBasis (word position))) • vector := by
    change (iteratedFDeriv ℝ order (fun target => scalar target • vector) point)
      (fun position => spatialBasis (word position)) = _
    rw [iteratedFDeriv_smul_const_apply
      (scalarSmooth.contDiffAt.of_le (by exact_mod_cast le_top))]
    rfl
  rw [applied, norm_smul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg vector)
  apply le_trans ((iteratedFDeriv ℝ order scalar point).le_opNorm _)
  calc ‖iteratedFDeriv ℝ order scalar point‖ *
      ∏ position, ‖spatialBasis (word position)‖ ≤
      ‖iteratedFDeriv ℝ order scalar point‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_one (fun position _ => norm_nonneg _)
          (fun position _ => spatialBasis_norm_le _)
    _ = ‖iteratedFDeriv ℝ order scalar point‖ := mul_one _

/-! ### The dilated product word bound -/

/-- Order-`n` derivatives of `W_n · (u ∘ λ_n)` for a fixed smooth compactly
supported `u` cost one uniform constant times `e^{σ₀ λ_n} λ_n^n`. -/
theorem dilated_product_word_bound (profile : SpatialPlane → ℝ)
    (profileSmooth : ContDiff ℝ ∞ profile)
    (profileCompact : HasCompactSupport profile) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (cell : ℤ) (point : SpatialPlane),
      ‖iteratedFDeriv ℝ order (fun target =>
          cartesianWeight parameters cell target *
            profile (cellFrequency cell • target)) point‖ ≤
        bound * Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ order := by
  choose profileBound profileBoundNonneg profileBoundLe using
    fun rank => compact_word_bound profile profileSmooth profileCompact rank
  refine ⟨∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
    weightWordConstant parameters index * profileBound (order - index), ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro index _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (weightWordConstant_nonneg parameters index)) (profileBoundNonneg _)
  intro cell point
  have dilatedSmooth : ContDiff ℝ ∞
      (fun target => profile (cellFrequency cell • target)) :=
    profileSmooth.comp (contDiff_id.const_smul (cellFrequency cell))
  have productBound := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
    (cartesianWeight_contDiff parameters cell) dilatedSmooth point
    (n := order) (by exact_mod_cast le_top)
  apply productBound.trans
  have termBound : ∀ index ∈ Finset.range (order + 1),
      (order.choose index : ℝ) *
        ‖iteratedFDeriv ℝ index (cartesianWeight parameters cell) point‖ *
        ‖iteratedFDeriv ℝ (order - index)
          (fun target => profile (cellFrequency cell • target)) point‖ ≤
      (order.choose index : ℝ) * weightWordConstant parameters index *
        profileBound (order - index) *
        (Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ order) := by
    intro index indexIn
    have indexLe : index ≤ order := by
      have := Finset.mem_range.mp indexIn
      omega
    have weightPart := weight_iterated_opnorm_bound parameters cell index point
    have dilatedEq := iteratedFDeriv_comp_const_smul (i := order - index)
      (cellFrequency cell) (profileSmooth.of_le (natCast_le_infty (order - index)))
    have dilatedPart : ‖iteratedFDeriv ℝ (order - index)
        (fun target => profile (cellFrequency cell • target)) point‖ ≤
        cellFrequency cell ^ (order - index) * profileBound (order - index) := by
      have pointEq := congrFun dilatedEq point
      rw [pointEq, norm_smul, Real.norm_of_nonneg
        (pow_nonneg (cellFrequency_pos cell).le _)]
      exact mul_le_mul_of_nonneg_left (profileBoundLe _ _)
        (pow_nonneg (cellFrequency_pos cell).le _)
    have powerSplit : cellFrequency cell ^ index *
        cellFrequency cell ^ (order - index) = cellFrequency cell ^ order := by
      rw [← pow_add, Nat.add_sub_cancel' indexLe]
    have leftNonneg : (0 : ℝ) ≤ (order.choose index : ℝ) *
        (weightWordConstant parameters index *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ index) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg
        (weightWordConstant_nonneg parameters index) (Real.exp_pos _).le)
        (pow_nonneg (cellFrequency_pos cell).le _))
    calc (order.choose index : ℝ) *
        ‖iteratedFDeriv ℝ index (cartesianWeight parameters cell) point‖ *
        ‖iteratedFDeriv ℝ (order - index)
          (fun target => profile (cellFrequency cell • target)) point‖ ≤
        (order.choose index : ℝ) *
          (weightWordConstant parameters index *
            Real.exp (parameters.sigma0 * cellFrequency cell) *
            cellFrequency cell ^ index) *
          (cellFrequency cell ^ (order - index) * profileBound (order - index)) := by
          apply mul_le_mul _ dilatedPart (norm_nonneg _) leftNonneg
          exact mul_le_mul_of_nonneg_left weightPart (Nat.cast_nonneg _)
      _ = (order.choose index : ℝ) * weightWordConstant parameters index *
          profileBound (order - index) *
          (Real.exp (parameters.sigma0 * cellFrequency cell) *
            (cellFrequency cell ^ index * cellFrequency cell ^ (order - index))) := by
          ring
      _ = (order.choose index : ℝ) * weightWordConstant parameters index *
          profileBound (order - index) *
          (Real.exp (parameters.sigma0 * cellFrequency cell) *
            cellFrequency cell ^ order) := by
          rw [powerSplit]
  apply le_trans (Finset.sum_le_sum termBound)
  rw [← Finset.sum_mul]
  apply le_of_eq
  ring

end Grad.AxisJet
