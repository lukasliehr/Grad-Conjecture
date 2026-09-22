import AIP10DiskCoefficientFunctional

noncomputable section
open Set MeasureTheory

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization

theorem zeroCoefficient_continuous (mode : FourierMode) :
    Continuous (fun field : JGrade (ComplexEuclidean 1) 0 => coefficient 0 field mode 0) := by
  have evaluation := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp
    (lp.evalCLM ℂ (fun _ : FourierMode => ComplexEuclidean 1) 2 mode).continuous)
  change Continuous (fun field : JGrade (ComplexEuclidean 1) 0 => field mode 0) at evaluation
  simpa only [coefficient, pow_zero, inv_one, one_smul] using evaluation

/-- Exact Fourier coefficients of the bounded extension of an actual disk L2
field after the supported cutoff, proved by the genuine dense smooth core. -/
theorem diskFourier_cutoff_coefficient (parameters : PhaseParameters) (field : DiskL2 1)
    (mode : FourierMode) :
    coefficient 0 (diskFourier parameters
      (diskScalar periodizationCutoff.toFun periodizationCutoff.smooth field)) mode 0 =
      if mode.2.2 = 0 then actualDiskCoefficient mode.1 mode.2.1
        (diskScalar periodizationCutoff.toFun periodizationCutoff.smooth field) else 0 := by
  have leftContinuous := (zeroCoefficient_continuous mode).comp
    ((diskFourier parameters).continuous.comp
      (diskScalar periodizationCutoff.toFun periodizationCutoff.smooth).continuous)
  have rightContinuous : Continuous (fun field : DiskL2 1 =>
      if mode.2.2 = 0 then actualDiskCoefficient mode.1 mode.2.1
        (diskScalar periodizationCutoff.toFun periodizationCutoff.smooth field) else 0) := by
    by_cases zero : mode.2.2 = 0
    · simp only [if_pos zero]
      exact (actualDiskCoefficient mode.1 mode.2.1).continuous.comp
        (diskScalar periodizationCutoff.toFun periodizationCutoff.smooth).continuous
    · simp only [if_neg zero]
      exact continuous_const
  apply isClosed_property closedL2Core_denseRange (isClosed_eq leftContinuous rightContinuous) _ field
  intro core
  dsimp only [Function.comp_def]
  rw [← periodizationCore_L2]
  rw [diskFourier_compact_single_cell parameters (periodizationCore core) (periodizationCore_supported core)]
  by_cases zero : mode.2.2 = 0
  · simp only [if_pos zero]
    exact spatialCoreCoefficient_coordinate (periodizationCore core) (periodizationCore_supported core) _ _
  · simp only [if_neg zero, PiLp.zero_apply]

/-- The actual supported field has no artificial cell modes. -/
theorem diskFourier_supported_coefficient (parameters : PhaseParameters) (field : DiskL2 1)
    (supported : diskScalar periodizationCutoff.toFun periodizationCutoff.smooth field = field)
    (mode : FourierMode) :
    coefficient 0 (diskFourier parameters field) mode 0 =
      if mode.2.2 = 0 then actualDiskCoefficient mode.1 mode.2.1 field else 0 := by
  simpa only [supported] using diskFourier_cutoff_coefficient parameters field mode

end Grad.InteriorPeriodization
