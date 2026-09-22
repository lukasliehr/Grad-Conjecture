import AKDK10PureCellTerminalAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.OriginalCartesianTameEstimate
open Grad.GaugeCoefficients.Physical.Allocation

/-- The homogeneous terminal is the SAME Fourier field, over any radial
measure (including r dr). All coefficient/ν allocations are paid jointly. -/
theorem nativePureTerminal_jointEnergy {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset grade order power : ℕ)
    (gradePositive : 0<grade) (paid : order+power≤grade)
    (small : physicalBudget parameters field rho epsilon offset≤1)
    (measure : Measure ℝ) (base middle high : ℝ → CellL2 dimension)
    (baseMeasurable : AEStronglyMeasurable base measure) (highMeasurable : AEStronglyMeasurable high measure)
    (middleSame : ∀ᵐ radius ∂measure, ∀ mode : ℤ × ℤ, middle radius mode=(annularFrequency mode.1 mode.2 : ℂ)^power • base radius mode)
    (highSame : ∀ᵐ radius ∂measure, ∀ mode : ℤ × ℤ, high radius mode=(annularFrequency mode.1 mode.2 : ℂ)^grade • base radius mode)
    (highPayment basePayment : ℝ) (high0 : 0≤highPayment) (base0 : 0≤basePayment)
    (highEnergy : (∫⁻ radius, ENNReal.ofReal (‖high radius‖^2) ∂measure) ≤ ENNReal.ofReal (highPayment^2))
    (baseEnergy : (∫⁻ radius, ENNReal.ofReal (‖base radius‖^2) ∂measure) ≤ ENNReal.ofReal (basePayment^2)) :
    (∫⁻ radius, ENNReal.ofReal (‖(1+physicalBudget parameters field rho epsilon (offset+order)) • middle radius‖^2) ∂measure) ≤
      ENNReal.ofReal ((4*(1+physicalInterpolationConstant offset grade)*
        (highPayment+(1+physicalBudget parameters field rho epsilon (offset+grade))*basePayment))^2) := by
  have bound : ∀ᵐ radius ∂measure,
      ‖(1+physicalBudget parameters field rho epsilon (offset+order)) • middle radius‖≤
        (2*(1+physicalInterpolationConstant offset grade))*
          (‖high radius‖+(1+physicalBudget parameters field rho epsilon (offset+grade))*‖base radius‖) := by
    filter_upwards [middleSame,highSame] with radius middleSame highSame
    exact pureCell_jointAllocation parameters field rho epsilon offset grade order power gradePositive paid small
      (base radius) (middle radius) (high radius) middleSame highSame
  have result := twoInput_squareEnergy measure
    (fun radius => (1+physicalBudget parameters field rho epsilon (offset+order)) • middle radius) high base
    highMeasurable baseMeasurable (2*(1+physicalInterpolationConstant offset grade))
    (1+physicalBudget parameters field rho epsilon (offset+grade)) highPayment basePayment
    (mul_nonneg (by norm_num) (add_nonneg zero_le_one (zero_le_one.trans (physicalInterpolationConstant_one_le offset grade))))
    (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) high0 base0 bound highEnergy baseEnergy
  exact result.trans_eq (by congr 1; ring)

end Grad.OriginalTerminalAllocation
