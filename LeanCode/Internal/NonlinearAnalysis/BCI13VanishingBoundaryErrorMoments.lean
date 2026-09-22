import BCI12VanishingCoefficientMoments

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

 theorem actualRowCorrection_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact (fun state => state.rowCorrection) := by
  unfold PhysicalBoundaryState.rowCorrection
  exact UniformKernelMoments.add
    (BoundaryDeviationMoments.comp_regular (boundaryRotatedDeviationMultiplier_vanishingMoments parameters L compact)
      (BoundaryKernelMoments.of_reconstruction (actualUnknownUKernel_physicalMoments parameters L compact)))
    (BoundaryDeviationMoments.comp_regular (boundaryDeviationMultiplier_vanishingMoments parameters L compact)
      (BoundaryKernelMoments.of_reconstruction (actualUnknownVKernel_physicalMoments parameters L compact)))

theorem actualMassPerturbation_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact (fun state => state.massPerturbation) := by
  unfold PhysicalBoundaryState.massPerturbation actualMassPerturbationKernel
  dsimp only
  apply BoundaryDeviationMoments.regular_comp (BoundaryKernelMoments.fixed parameters L compact (angularMeanFreeKernel parameters 1))
  exact UniformKernelMoments.add
    (BoundaryDeviationMoments.comp_regular (actualRotatedSigmaBoundaryKernel_vanishingMoments parameters L compact)
      (BoundaryKernelMoments.of_reconstruction (actualUnknownUKernel_physicalMoments parameters L compact)))
    (BoundaryDeviationMoments.comp_regular (actualSigmaBoundaryKernel_vanishingMoments parameters L compact)
      (BoundaryKernelMoments.of_reconstruction (actualUnknownVKernel_physicalMoments parameters L compact)))

theorem actualKnownJStar_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact (fun state => state.knownJ) := by
  unfold PhysicalBoundaryState.knownJ actualKnownJStarKernel
  dsimp only
  apply BoundaryDeviationMoments.regular_comp (BoundaryKernelMoments.fixed parameters L compact (angularMeanFreeKernel parameters 1))
  apply UniformKernelMoments.add
  · exact UniformKernelMoments.add
      (BoundaryDeviationMoments.comp_regular (actualRotatedSigmaBoundaryKernel_vanishingMoments parameters L compact)
        (BoundaryKernelMoments.of_reconstruction (actualKnownAStarKernel_physicalMoments parameters L compact)))
      (BoundaryDeviationMoments.comp_regular (actualSigmaBoundaryKernel_vanishingMoments parameters L compact)
        (BoundaryKernelMoments.of_reconstruction (actualKnownRAStarKernel_physicalMoments parameters L compact)))
  · exact UniformKernelMoments.add
      (BoundaryDeviationMoments.comp_regular (actualRotatedSigmaComponentBoundaryKernel_vanishingMoments parameters L compact 1)
        (BoundaryKernelMoments.fixed parameters L compact (sevenInputSlotKernel parameters 3)))
      (BoundaryDeviationMoments.comp_regular (actualSigmaComponentBoundaryKernel_vanishingMoments parameters L compact 1)
        (BoundaryKernelMoments.fixed parameters L compact (sevenInputSlotKernel parameters 1)))

/-- Every high boundary error moment is C_q B(q+7), with the high factor
allocated before the physical coefficient bounds. -/
theorem actualBoundaryE_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryDeviationMoments parameters L compact (fun state => state.boundaryE) := by
  unfold PhysicalBoundaryState.boundaryE
  exact BoundaryDeviationMoments.regular_comp (BoundaryKernelMoments.fixed parameters L compact (highAngularKernel parameters 1))
    (BoundaryDeviationMoments.comp_regular
      (BoundaryDeviationMoments.comp_regular
        (UniformKernelMoments.add (actualMassPerturbation_vanishingMoments parameters L compact)
          (actualRowCorrection_vanishingMoments parameters L compact))
        (BoundaryKernelMoments.of_reconstruction (actualMassInverseKernel_physicalMoments parameters L compact)))
      (BoundaryKernelMoments.fixed parameters L compact (highAngularKernel parameters 1)))

theorem BoundaryDeviationMoments.regular {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {family : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters input output}
    (bounded : BoundaryDeviationMoments parameters L compact family) : BoundaryKernelMoments parameters L compact family := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ := bounded moment
  refine ⟨constant, nonnegative, fun state => (bound state).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (by change state.budget moment ≤ 1 + state.budget moment; linarith) nonnegative

theorem fullKernel_eq_zero_of_moment_zero {parameters : PhaseParameters} {input output : ℕ}
    (kernel : FullTwoFrequencyKernel parameters input output) (zero : fullKernelMoment parameters 0 kernel ≤ 0) :
    kernel = fullZeroKernel parameters input output := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift frequency
  rw [fullZeroKernel_entry]
  exact norm_le_zero_iff.mp ((kernel.entry_le shift frequency).trans
    ((fullKernelMoment_entryNorm_le parameters kernel shift).trans zero))

theorem BoundaryDeviationMoments.reference_zero {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {family : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters input output}
    (bounded : BoundaryDeviationMoments parameters L compact family)
    (state : PhysicalBoundaryState parameters L compact) (reference : state.budget 0 = 0) :
    family state = fullZeroKernel parameters input output := by
  obtain ⟨constant, _, bound⟩ := bounded 0
  apply fullKernel_eq_zero_of_moment_zero
  simpa only [reference, mul_zero] using bound state

end Grad.ActualBoundaryInverse
