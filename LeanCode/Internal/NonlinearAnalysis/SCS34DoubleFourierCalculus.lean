import SCS33PhysicalProduct

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem angularCoefficient_compact_general {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (field : ℝ → Value) (mode : ℤ) :
    angularCoefficient field mode = (2 * Real.pi)⁻¹ •
      ∫ angle in Icc (-Real.pi) Real.pi, cellExponential (-mode) angle • field angle := by
  rw [angularCoefficient_integral, intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le,
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [show fourier (-mode) (angle : CellCircle) = cellExponential (-mode) angle from cellCharacter_coe _ _]

theorem doubleCoefficient_swap {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [CompleteSpace Value] (field : ℝ × ℝ → Value)
    (continuousField : Continuous field) (first second : ℤ) :
    angularCoefficient (fun polar => angularCoefficient (fun axial => field (polar, axial)) second) first =
      angularCoefficient (fun axial => angularCoefficient (fun polar => field (polar, axial)) first) second := by
  let integrand : ℝ × ℝ → Value := fun angles =>
    cellExponential (-first) angles.1 • (cellExponential (-second) angles.2 • field angles)
  have continuousIntegrand : Continuous integrand :=
    ((cellExponential_smooth (-first)).continuous.comp continuous_fst).smul
      (((cellExponential_smooth (-second)).continuous.comp continuous_snd).smul continuousField)
  have integrable : Integrable integrand
      ((volume.restrict (Icc (-Real.pi) Real.pi)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact continuousIntegrand.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have swap := integral_integral_swap (f := fun polar axial => integrand (polar, axial)) integrable
  have commute (scalar : ℂ) (curve : ℝ → Value) :
      scalar • ((2 * Real.pi)⁻¹ • ∫ angle in Icc (-Real.pi) Real.pi, curve angle) =
        (2 * Real.pi)⁻¹ • ∫ angle in Icc (-Real.pi) Real.pi, scalar • curve angle := by
    rw [integral_smul, smul_comm]
  simp_rw [angularCoefficient_compact_general, commute, integral_smul]
  congr 2
  simp_rw [← integral_smul]
  exact swap.trans (integral_congr_ae (Filter.Eventually.of_forall (fun axial =>
    integral_congr_ae (Filter.Eventually.of_forall (fun polar =>
      smul_comm (cellExponential (-first) polar) (cellExponential (-second) axial) (field (polar, axial)))))))

end Grad.SourceCollarFullSource
