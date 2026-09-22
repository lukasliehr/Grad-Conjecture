import AHP33ActualRadialReconstructionConsumer

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- Projection onto the two physical gauge coordinates. -/
def gaugeTailProjectionMap : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 2 :=
  matrixUnit 0 1 + matrixUnit 1 2

def gaugeTailProjectionKernel (parameters : PhaseParameters) :
    FullTwoFrequencyKernel parameters 3 2 :=
  constantMatrixKernel parameters 3 2 gaugeTailProjectionMap

theorem gaugeTailProjection_injection (parameters : PhaseParameters) (angular cell : ℕ)
    (input : NegativeTrace parameters angular cell 2) :
    fullNegativeKernelAction parameters angular cell (gaugeTailProjectionKernel parameters)
      (fullNegativeKernelAction parameters angular cell (tailInjectionKernel parameters) input) = input := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [gaugeTailProjectionKernel, tailInjectionKernel,
    constantMatrixKernel_action_coefficient]
  apply PiLp.ext
  intro component
  fin_cases component <;>
    simp [gaugeTailProjectionMap, tailInjectionMap, matrixUnit_apply, operatorBasis]

theorem angularMean_action_constant_eq {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (input : NegativeTrace parameters angular cell dimension)
    (supported : IsAngularConstant parameters angular cell input) :
    fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters dimension) input = input := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  rw [angularMeanKernel, scalarModeDiagonalKernel_action_coefficient]
  by_cases zero : mode.1 = 0
  · simp [angularMeanMultiplier, zero]
  · simp [angularMeanMultiplier, zero, supported mode zero]

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

/-- Mean multiplication by the original gauge deviation on a constant tail
is exactly the already constructed Gamma deviation, including every cell mode. -/
theorem radialGaugeMeanRows_tail_constant (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 2)
    (supported : IsAngularConstant (rp parameters r) angular cell input) :
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialGaugeMeanRowsKernel parameters L compact state r)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (tailInjectionKernel (rp parameters r)) input) =
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialGammaDeviationKernel parameters L compact state r) input := by
  apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
  intro mode
  unfold radialGaugeMeanRowsKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    angularMeanKernel, scalarModeDiagonalKernel_action_coefficient]
  have left := (fullNegativeKernelAction_coefficient_hasSum (rp parameters r) angular cell
    (radialGaugeRowsKernel parameters L compact state r 0)
    (fullNegativeKernelAction (rp parameters r) angular cell
      (tailInjectionKernel (rp parameters r)) input) mode).const_smul (angularMeanMultiplier mode)
  have right := fullNegativeKernelAction_coefficient_hasSum (rp parameters r) angular cell
    (radialGammaDeviationKernel parameters L compact state r) input mode
  apply left.unique
  convert right using 1
  funext shift
  rw [tailInjectionKernel, constantMatrixKernel_action_coefficient]
  by_cases inputZero : (twoFrequencyTranslation shift mode).1 = 0
  · have same : mode.1 = shift.1 := by
      simpa only [twoFrequencyTranslation_apply, sub_eq_zero] using inputZero
    unfold radialGaugeRowsKernel radialGammaDeviationKernel radialMatrixKernel
    rw [boundaryMatrixMultiplicationKernel_entry_apply,
      boundaryMatrixMultiplicationKernel_entry_apply]
    by_cases shiftZero : shift.1 = 0
    · have modeZero : mode.1 = 0 := same.trans shiftZero
      simp only [angularMeanMultiplier, if_pos modeZero, one_smul]
      apply Finset.sum_congr rfl
      intro row _
      congr 1
      simp [radialGammaCoefficients, shiftZero, tailInjectionMap,
        Fin.sum_univ_three, Fin.sum_univ_two, matrixUnit_apply, operatorBasis]
    · have modeNonzero : mode.1 ≠ 0 := by simpa only [same] using shiftZero
      simp [angularMeanMultiplier, modeNonzero, radialGammaCoefficients, shiftZero]
  · rw [supported _ inputZero]
    simp

/-- The literal original gauge means, with the circular tail rows restored. -/
def radialPhysicalGaugeMeans (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3) :
    NegativeTrace (rp parameters r) angular cell 2 :=
  fullNegativeKernelAction (rp parameters r) angular cell (angularMeanKernel (rp parameters r) 2)
    (fullNegativeKernelAction (rp parameters r) angular cell (gaugeTailProjectionKernel (rp parameters r)) input) +
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialGaugeMeanRowsKernel parameters L compact state r) input

end Grad.AnnularReconstruction
