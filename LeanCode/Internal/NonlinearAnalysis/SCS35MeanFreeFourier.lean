import SCS34DoubleFourierCalculus

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollar

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value] [CompleteSpace Value]

theorem angularCoefficient_constant (value : Value) (mode : ℤ) :
    angularCoefficient (fun _ : ℝ => value) mode = if mode = 0 then value else 0 := by
  rw [angularCoefficient_circle (fun _ : CellCircle => value)]
  have expression : (fun _ : CellCircle => value) = (fun angle : CellCircle => fourier 0 angle • value) := by
    funext angle
    simp
  rw [expression]
  have scalarLaw : fourierCoeff (fun angle : CellCircle => fourier 0 angle • value) mode =
      fourierCoeff (fourier 0 : CellCircle → ℂ) mode • value := by
    simp only [fourierCoeff, smul_smul, smul_eq_mul]
    exact integral_smul_const _ _
  rw [scalarLaw, fourierCoeff_fourier]
  split_ifs <;> simp_all

omit [CompleteSpace Value] in
theorem angularCoefficient_sub_general (first second : ℝ → Value)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (mode : ℤ) :
    angularCoefficient (fun angle => first angle - second angle) mode =
      angularCoefficient first mode - angularCoefficient second mode := by
  simp_rw [angularCoefficient_compact_general, smul_sub]
  have firstIntegrable : IntegrableOn (fun angle => cellExponential (-mode) angle • first angle)
      (Icc (-Real.pi) Real.pi) :=
    (((cellExponential_smooth (-mode)).continuous.smul firstContinuous).continuousOn.integrableOn_Icc)
  have secondIntegrable : IntegrableOn (fun angle => cellExponential (-mode) angle • second angle)
      (Icc (-Real.pi) Real.pi) :=
    (((cellExponential_smooth (-mode)).continuous.smul secondContinuous).continuousOn.integrableOn_Icc)
  rw [integral_sub firstIntegrable secondIntegrable, smul_sub]

theorem angularCoefficient_remove_mean (field : ℝ → Value) (continuousField : Continuous field) (mode : ℤ) :
    angularCoefficient (fun angle => field angle - angularCoefficient field 0) mode =
      if mode = 0 then 0 else angularCoefficient field mode := by
  rw [angularCoefficient_sub_general field _ continuousField continuous_const, angularCoefficient_constant]
  split_ifs with zero
  · subst mode
    exact sub_self _
  · exact sub_zero _

theorem sourceAngularAverage_eq_coefficient (field : ℝ → ℂ)
    (periodic : Function.Periodic field (2 * Real.pi)) :
    sourceAngularAverage field = angularCoefficient field 0 := by
  rw [sourceAngularAverage, angularCoefficient_integral]
  simp only [neg_zero, fourier_zero, one_smul]
  congr 1
  have shift := periodic.intervalIntegral_add_eq 0 (-Real.pi)
  simpa only [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] using shift

theorem sourceAngularMeanFree_coefficient (field : ℝ → ℂ)
    (continuousField : Continuous field) (periodic : Function.Periodic field (2 * Real.pi)) (mode : ℤ) :
    angularCoefficient (sourceAngularMeanFree field) mode = if mode = 0 then 0 else angularCoefficient field mode := by
  unfold sourceAngularMeanFree
  rw [sourceAngularAverage_eq_coefficient field periodic]
  exact angularCoefficient_remove_mean field continuousField mode

end Grad.SourceCollarFullSource
