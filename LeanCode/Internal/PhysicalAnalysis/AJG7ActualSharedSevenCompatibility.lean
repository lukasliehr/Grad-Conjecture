import AJG6ActualSharedSourceAngularLaw

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularCurrentSource
open Grad.AnnularSourceGraph Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularCrossMaps Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularCoupledInverse Grad.AnnularKnownLow

theorem highCrossSevenInput_compatible_ae (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      SevenModeCompatible mode (highCrossSevenInput lower length positive lengthPositive field mode radius) := by
  rw [ae_all_iff]
  intro mode
  by_cases high : 3 ≤ |mode.1|
  · filter_upwards [highCrossSevenInput_ae lower length positive lengthPositive field ⟨mode,high⟩] with radius actual
    rw [actual]
    exact crossSevenSymbol_compatible radius mode (by intro zero; norm_num [zero] at high) _ _
  · rw [highCrossSevenInput_outside lower length positive lengthPositive field mode high]
    filter_upwards [Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))] with radius zero
    rw [zero]
    exact SevenModeCompatible.zero mode

theorem lowNormalizedSevenInput_compatible_ae (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      SevenModeCompatible mode (lowNormalizedSevenInput parameters lower length lengthPositive positive field mode radius) := by
  rw [ae_all_iff]
  intro mode
  by_cases low : |mode.1| = 1 ∨ |mode.1| = 2
  · filter_upwards [lowNormalizedSevenInput_ae parameters lower length lengthPositive positive field ⟨mode,low⟩] with radius actual
    rw [actual]
    exact lowSevenInputSymbol_compatible parameters lower length positive ⟨mode,low⟩ radius _ _
  · rw [lowNormalizedSevenInput_outside parameters lower length lengthPositive positive field mode low]
    filter_upwards [Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))] with radius zero
    rw [zero]
    exact SevenModeCompatible.zero mode

theorem sharedKnownSeven_compatible_ae (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      SevenModeCompatible mode
        (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data) mode radius) := by
  filter_upwards [knownLowSevenPacket_ae lower (strongKnownBulk parameters lower positive bounded data),
    strongKnownBulk_genuineAngular parameters lower positive bounded data,
    Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))] with radius packet derivative zero
  intro mode
  rw [packet mode]
  apply knownSevenSymbol_compatible
  · exact congrArg (fun value : ComplexEuclidean 1 => value 0) (derivative mode)
  · intro mean
    rw [strongKnownBulk_second_meanFree parameters lower positive bounded data mode mean, zero]
    rfl

private theorem radialRow_add_ae {dimension : ℕ} (lower : ℝ) (first second : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      (first + second) mode radius = first mode radius + second mode radius := by
  rw [ae_all_iff]
  intro mode
  exact Lp.coeFn_add (first mode) (second mode)

/-- The completed seven-input field built from arbitrary actual high/low
graphs and the SAME shared strong datum satisfies every reconstruction
support and angular-derivative condition almost everywhere. -/
theorem fullStrongSevenInput_compatible_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower length positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      BulkSevenCompatibility
        (collectRadial lower (fullStrongSevenInput parameters length lower lengthPositive positive bounded data solution) radius) := by
  let high := highCrossSevenInput lower length positive lengthPositive solution.ofLp.1
  let low := lowNormalizedSevenInput parameters lower length lengthPositive positive (solution.ofLp.2.val 0)
  let known := knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded data)
  have same : fullStrongSevenInput parameters length lower lengthPositive positive bounded data solution = high + low + known := rfl
  rw [same]
  filter_upwards [collectRadial_ae lower (high + low + known),
    highCrossSevenInput_compatible_ae lower length positive lengthPositive solution.ofLp.1,
    lowNormalizedSevenInput_compatible_ae parameters lower length lengthPositive positive (solution.ofLp.2.val 0),
    sharedKnownSeven_compatible_ae parameters lower positive bounded data,
    radialRow_add_ae lower high low, radialRow_add_ae lower (high + low) known]
    with radius collected highCompatible lowCompatible knownCompatible firstSum fullSum
  apply bulkSevenCompatibility_of_modes
  intro mode
  rw [collected mode, fullSum mode, firstSum mode]
  exact SevenModeCompatible.add mode _ _
    (SevenModeCompatible.add mode _ _ (highCompatible mode) (lowCompatible mode)) (knownCompatible mode)

end Grad.AnnularPhysicalReconstruction
