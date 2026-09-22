import SCS35MeanFreeFourier

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollar

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]

theorem angularCoefficient_continuous_parameter (field : ℝ × ℝ → Value)
    (continuousField : Continuous field) (mode : ℤ) :
    Continuous (fun parameter => angularCoefficient (fun angle => field (parameter, angle)) mode) := by
  simp_rw [angularCoefficient_compact_general]
  exact (continuous_const : Continuous (fun _ : ℝ => (2 * Real.pi)⁻¹)).smul
    (continuous_parametric_integral_of_continuous
      (((cellExponential_smooth (-mode)).continuous.comp continuous_snd).smul continuousField) isCompact_Icc)

def removePolarMean (field : ℝ × ℝ → Value) (angles : ℝ × ℝ) : Value :=
  field angles - angularCoefficient (fun polar => field (polar, angles.2)) 0

theorem removePolarMean_continuous (field : ℝ × ℝ → Value) (continuousField : Continuous field) :
    Continuous (removePolarMean field) :=
  continuousField.sub ((angularCoefficient_continuous_parameter (fun pair => field (pair.2, pair.1))
    (continuousField.comp continuous_swap) 0).comp continuous_snd)

/-- The zero angular mode is removed after the physical product. The axial
Fourier index remains unrestricted, including its own zero mode. -/
theorem doubleCoefficient_removePolarMean [CompleteSpace Value] (field : ℝ × ℝ → Value)
    (continuousField : Continuous field) (mode : ℤ × ℤ) :
    angularCoefficient (fun polar => angularCoefficient (fun axial => removePolarMean field (polar, axial)) mode.2) mode.1 =
      if mode.1 = 0 then 0 else
        angularCoefficient (fun polar => angularCoefficient (fun axial => field (polar, axial)) mode.2) mode.1 := by
  rw [doubleCoefficient_swap (removePolarMean field) (removePolarMean_continuous field continuousField)]
  have projected (axial : ℝ) :
      angularCoefficient (fun polar => removePolarMean field (polar, axial)) mode.1 =
        if mode.1 = 0 then 0 else angularCoefficient (fun polar => field (polar, axial)) mode.1 :=
    angularCoefficient_remove_mean (fun polar => field (polar, axial))
      (continuousField.comp (continuous_id.prodMk continuous_const)) mode.1
  simp_rw [projected]
  split_ifs with zero
  · rw [angularCoefficient_constant]
    split_ifs <;> rfl
  · exact (doubleCoefficient_swap field continuousField mode.1 mode.2).symm

end Grad.SourceCollarFullSource
