import AHR1PositiveAnnulusNormalization

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

/-- The actual reciprocal-radius normalization has a fixed collar bound.
This preserves the normalized one-high physical size without changing width. -/
theorem RadialPhysicalMoments.originalSlots {parameters : PhaseParameters} {L compact : ℝ}
    {output : ℕ}
    {family : (state : AnnularReconstructionState parameters L compact) →
      (r : RadialPoint) → RadialKernel parameters r 7 output}
    (bounded : RadialPhysicalMoments parameters L compact family)
    (lower : ℝ) (positive : 0 < lower) :
    ∀ moment, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint),
      lower ≤ r.val →
      fullKernelMoment (radialKernelParameters parameters r) moment
        (fullKernelComposition (family state r) (radialSevenSlotKernel parameters r)) ≤
        constant * state.val.size moment := by
  intro moment
  obtain ⟨high, highNonnegative, highBound⟩ := bounded moment
  obtain ⟨low, lowNonnegative, lowBound⟩ := bounded 0
  let normalizer := Real.exp (parameters.sigma0 + 2 * parameters.gamma) * (5 + 2 * lower⁻¹)
  let lowSize := 1 + actualMassInverseLowRadius parameters L compact
  have normalizerNonnegative : 0 ≤ normalizer := by dsimp [normalizer]; positivity
  have lowSizeNonnegative : 0 ≤ lowSize := by
    dsimp [lowSize]
    linarith [actualMassInverseLowRadius_positive parameters L compact]
  refine ⟨2 ^ moment * (high + low * lowSize) * normalizer, by positivity, ?_⟩
  intro state r inside
  have base := (lowBound state r).trans
    (mul_le_mul_of_nonneg_left state.val.size_zero_le lowNonnegative)
  have normalization (grade : ℕ) := radialSevenSlotKernel_moment_on_annulus parameters
    lower positive r inside grade
  have sizeNonnegative := state.val.size_nonnegative moment
  apply (fullKernelComposition_moment_le moment (family state r) (radialSevenSlotKernel parameters r)).trans
  calc
    _ ≤ 2 ^ moment * ((high * state.val.size moment) * normalizer + (low * lowSize) * normalizer) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul (highBound state r) (normalization 0)
          (fullKernelMoment_nonnegative _ _ _) (by positivity))
        (mul_le_mul base (normalization moment)
          (fullKernelMoment_nonnegative _ _ _) (by positivity))
    _ ≤ 2 ^ moment * ((high * state.val.size moment) * normalizer +
        ((low * lowSize) * normalizer) * state.val.size moment) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add le_rfl (le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg lowNonnegative lowSizeNonnegative) normalizerNonnegative)
        (state.val.one_le_size moment))
    _ = _ := by ring

theorem radialCovariantKernel_physicalMoments_on_annulus
    (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower) :
    ∀ moment, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint)
        (inside : lower ≤ r.val),
      fullKernelMoment (radialKernelParameters parameters r) moment
        (radialCovariantKernel parameters L compact state.val r state.property
          (positive.trans_le inside)) ≤ constant * state.val.size moment :=
  (radialNormalizedCovariantKernel_physicalMoments parameters L compact).originalSlots lower positive

theorem radialRotatedCovariantKernel_physicalMoments_on_annulus
    (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower) :
    ∀ moment, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint)
        (inside : lower ≤ r.val),
      fullKernelMoment (radialKernelParameters parameters r) moment
        (radialRotatedCovariantKernel parameters L compact state.val r state.property
          (positive.trans_le inside)) ≤ constant * state.val.size moment :=
  (radialNormalizedRotatedCovariantKernel_physicalMoments parameters L compact).originalSlots lower positive

/-- Exact original-slot C and RC on any fixed positive collar. The constant
is chosen before physical state and radius; the one-high budget is literal. -/
theorem originalSevenSlotKernel_oneHigh
    (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower) :
    ∀ moment, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : AnnularReconstructionState parameters L compact) (r : RadialPoint)
        (inside : lower ≤ r.val),
      fullKernelMoment (radialKernelParameters parameters r) moment
        (radialCovariantKernel parameters L compact state.val r state.property
          (positive.trans_le inside)) +
      fullKernelMoment (radialKernelParameters parameters r) moment
        (radialRotatedCovariantKernel parameters L compact state.val r state.property
          (positive.trans_le inside)) ≤
      constant * (1 + physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 7)) := by
  intro moment
  obtain ⟨first, firstNonnegative, firstBound⟩ :=
    radialCovariantKernel_physicalMoments_on_annulus parameters L compact lower positive moment
  obtain ⟨second, secondNonnegative, secondBound⟩ :=
    radialRotatedCovariantKernel_physicalMoments_on_annulus parameters L compact lower positive moment
  refine ⟨first + second, add_nonneg firstNonnegative secondNonnegative, ?_⟩
  intro state r inside
  exact (add_le_add (firstBound state r inside) (secondBound state r inside)).trans_eq (add_mul _ _ _).symm

end Grad.AnnularReconstruction
