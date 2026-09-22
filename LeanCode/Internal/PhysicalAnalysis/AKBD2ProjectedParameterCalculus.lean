import AKBD1CorrectedDeterminantCancellation
import CompactSmoothIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualDeterminantEquations
open Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource Grad.Constraints

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℂ Value] [CompleteSpace Value]

omit [CompleteSpace Value] in
theorem angularMean_integral (field : ℝ → Value) :
    angularCoefficient field 0 = (2*Real.pi)⁻¹ • ∫ angle in Icc (-Real.pi) Real.pi, field angle := by
  rw [angularCoefficient_compact_general]
  simp [cellExponential]

omit [CompleteSpace Value] in
/-- Differentiation of the actual angular mean on any open radial interval.
The derivative is supplied pointwise and justified by existing compact integration. -/
theorem angularMean_hasDerivAt_on (field : ℝ × ℝ → Value) (domain : Set ℝ)
    (openDomain : IsOpen domain) (smooth : ContDiffOn ℝ ∞ field (domain ×ˢ univ))
    (time : ℝ) (inside : time ∈ domain) (slope : ℝ → Value)
    (derivative : ∀ angle, HasDerivAt (fun value => field (value,angle)) (slope angle) time) :
    HasDerivAt (fun value => angularCoefficient (fun angle => field (value,angle)) 0)
      (angularCoefficient slope 0) time := by
  have integralDerivative := hasFDerivAt_compactIntegral openDomain smooth (-Real.pi) Real.pi time inside
  have derivativeContinuous : Continuous (fun angle : ℝ => integralParameterDerivative field (time,angle)) :=
    (integralParameterDerivative_smooth openDomain smooth).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)
  have derivativeIntegrable : IntegrableOn (fun angle : ℝ => integralParameterDerivative field (time,angle)) (Icc (-Real.pi) Real.pi) :=
    derivativeContinuous.continuousOn.integrableOn_Icc
  have pointwise (angle : ℝ) : integralParameterDerivative field (time,angle) 1 = slope angle := by
    have differential := (smooth.contDiffAt ((openDomain.prod isOpen_univ).mem_nhds
      (show (time,angle) ∈ domain ×ˢ (univ : Set ℝ) from ⟨inside,mem_univ _⟩))).differentiableAt (by simp)
    rw [integralParameterDerivative_eq time angle differential,(derivative angle).hasFDerivAt.fderiv]
    simp
  simp_rw [angularMean_integral]
  apply (integralDerivative.hasDerivAt.const_smul ((2*Real.pi)⁻¹)).congr_deriv
  rw [ContinuousLinearMap.integral_apply derivativeIntegrable]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  exact pointwise angle

omit [CompleteSpace Value] in
theorem removePolarMean_add (first second : ℝ × ℝ → Value)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) :
    removePolarMean (fun angles => first angles+second angles) =
      fun angles => removePolarMean first angles+removePolarMean second angles := by
  funext angles
  unfold removePolarMean
  rw [angularCoefficient_add_general (fun polar => first (polar,angles.2)) (fun polar => second (polar,angles.2))
    (firstContinuous.comp (continuous_id.prodMk continuous_const))
    (secondContinuous.comp (continuous_id.prodMk continuous_const))]
  abel_nf
  simp only [add_assoc]

omit [CompleteSpace Value] in
theorem removePolarMean_sub (first second : ℝ × ℝ → Value)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) :
    removePolarMean (fun angles => first angles-second angles) =
      fun angles => removePolarMean first angles-removePolarMean second angles := by
  funext angles
  unfold removePolarMean
  rw [angularCoefficient_sub_general (fun polar => first (polar,angles.2)) (fun polar => second (polar,angles.2))
    (firstContinuous.comp (continuous_id.prodMk continuous_const))
    (secondContinuous.comp (continuous_id.prodMk continuous_const))]
  abel_nf
  simp only [add_assoc]

omit [CompleteSpace Value] in
theorem removePolarMean_smul (scalar : ℂ) (field : ℝ × ℝ → Value) :
    removePolarMean (fun angles => scalar • field angles) =
      fun angles => scalar • removePolarMean field angles := by
  funext angles
  unfold removePolarMean
  simp only [angularMean_integral,integral_smul]
  rw [smul_comm,smul_sub]

theorem removePolarMean_idempotent (field : ℝ × ℝ → Value) (continuousField : Continuous field) :
    removePolarMean (removePolarMean field) = removePolarMean field := by
  funext angles
  change _ - angularCoefficient (fun polar => field (polar,angles.2)-angularCoefficient (fun theta => field (theta,angles.2)) 0) 0 = _
  rw [angularCoefficient_remove_mean (fun polar => field (polar,angles.2)) (continuousField.comp (continuous_id.prodMk continuous_const)),if_pos rfl,sub_zero]

end Grad.ActualDeterminantEquations
