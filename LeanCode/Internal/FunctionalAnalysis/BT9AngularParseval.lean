import BT8CollarGrade

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade

local instance angularPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def angularCoefficient {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (field : ℝ → Value) (mode : ℤ) : Value :=
  fourierCoeffOn (neg_lt_self Real.pi_pos) field mode

theorem angularCoefficient_integral {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (field : ℝ → Value) (mode : ℤ) :
    angularCoefficient field mode = (2 * Real.pi)⁻¹ •
      ∫ angle in -Real.pi..Real.pi, fourier (-mode) (angle : CellCircle) • field angle := by
  rw [angularCoefficient, fourierCoeffOn_eq_integral]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  simp only [one_div]

theorem angularCoefficient_circle {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (field : CellCircle → Value) (mode : ℤ) :
    angularCoefficient (fun angle : ℝ => field angle) mode = fourierCoeff field mode := by
  rw [angularCoefficient_integral, fourierCoeff_eq_intervalIntegral field mode (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  simp only [one_div]

theorem angularCoefficient_component {dimension : ℕ} (field : ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) (coordinate : Fin dimension) (mode : ℤ) :
    angularCoefficient field mode coordinate = angularCoefficient (fun angle => field angle coordinate) mode := by
  let projection : ComplexEuclidean dimension →L[ℂ] ℂ := euclideanComponent dimension coordinate
  have integrable : IntervalIntegrable (fun angle : ℝ => fourier (-mode) (angle : CellCircle) • field angle)
      volume (-Real.pi) Real.pi :=
    (((fourier (-mode)).continuous.comp (AddCircle.continuous_mk' _)).smul continuousField).intervalIntegrable _ _
  rw [angularCoefficient_integral, angularCoefficient_integral]
  change (projection.restrictScalars ℝ) ((2 * Real.pi)⁻¹ •
    ∫ angle in -Real.pi..Real.pi, fourier (-mode) (angle : CellCircle) • field angle) = _
  rw [map_smul]
  congr 1
  change projection (∫ angle in -Real.pi..Real.pi, fourier (-mode) (angle : CellCircle) • field angle) = _
  rw [← projection.intervalIntegral_comp_comm integrable]
  apply intervalIntegral.integral_congr
  intro angle _
  exact projection.map_smul _ _

theorem angular_hasSum_sq {dimension : ℕ} (field : ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) :
    HasSum (fun mode : ℤ => ‖angularCoefficient field mode‖ ^ 2)
      ((2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2) := by
  have coordinateContinuous (coordinate : Fin dimension) : Continuous (fun angle => field angle coordinate) :=
    (PiLp.continuous_apply (p := 2) (fun _ : Fin dimension => ℂ) coordinate).comp continuousField
  have componentSum (coordinate : Fin dimension) :
      HasSum (fun mode : ℤ => ‖angularCoefficient (fun angle => field angle coordinate) mode‖ ^ 2)
        ((2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖field angle coordinate‖ ^ 2) := by
    have member : MemLp (fun angle => field angle coordinate) 2
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
      apply (memLp_two_iff_integrable_sq_norm (coordinateContinuous coordinate).aestronglyMeasurable).mpr
      exact ((coordinateContinuous coordinate).norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have scalar := hasSum_sq_fourierCoeffOn (neg_lt_self Real.pi_pos) member
    simpa only [angularCoefficient, show Real.pi - -Real.pi = 2 * Real.pi by ring, smul_eq_mul] using scalar
  have sum := hasSum_sum (s := Finset.univ) (fun coordinate _ => componentSum coordinate)
  have termEquality : (fun mode : ℤ => ∑ coordinate : Fin dimension,
      ‖angularCoefficient (fun angle => field angle coordinate) mode‖ ^ 2) =
      fun mode : ℤ => ‖angularCoefficient field mode‖ ^ 2 := by
    funext mode
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro coordinate _
    rw [angularCoefficient_component field continuousField coordinate mode]
  have limitEquality : (∑ coordinate : Fin dimension,
      (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖field angle coordinate‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2 := by
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum]
    · congr 1
      apply intervalIntegral.integral_congr
      intro angle _
      exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin dimension => ℂ) (field angle)).symm
    · intro coordinate _
      exact ((coordinateContinuous coordinate).norm.pow 2).intervalIntegrable _ _
  rw [termEquality, limitEquality] at sum
  exact sum

theorem angular_bessel_finite {dimension : ℕ} (field : ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field) (modes : Finset ℤ) :
    (∑ mode ∈ modes, ‖angularCoefficient field mode‖ ^ 2) ≤
      (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2 := by
  have sum := angular_hasSum_sq field continuousField
  rw [← sum.tsum_eq]
  exact sum.summable.sum_le_tsum modes (fun _ _ => sq_nonneg _)

end Grad.BoundaryTrace
