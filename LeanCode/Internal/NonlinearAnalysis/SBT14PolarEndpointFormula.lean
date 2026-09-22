import SBT13EndpointMaps

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarAngular
open Grad.BoundaryTrace Grad.Constraints.Gauges

theorem angularCoefficient_valueMap {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ℝ → ComplexEuclidean sourceDimension) (continuousField : Continuous field) (mode : ℤ) :
    angularCoefficient (fun angle => mapping (field angle)) mode = mapping (angularCoefficient field mode) := by
  rw [angularCoefficient_compact, angularCoefficient_compact]
  have realLinear := (mapping.restrictScalars ℝ).map_smul ((2 * Real.pi)⁻¹)
    (∫ angle in Icc (-Real.pi) Real.pi, cellExponential (-mode) angle • field angle)
  change mapping ((2 * Real.pi)⁻¹ • ∫ angle in Icc (-Real.pi) Real.pi,
    cellExponential (-mode) angle • field angle) = _ at realLinear
  rw [realLinear]
  congr 1
  have commutes := mapping.integral_comp_comm (μ := volume.restrict (Icc (-Real.pi) Real.pi))
    (((cellExponential_smooth (-mode)).continuous.smul continuousField).continuousOn.integrableOn_Icc)
  change (∫ angle in Icc (-Real.pi) Real.pi, mapping (cellExponential (-mode) angle • field angle)) =
    mapping (∫ angle in Icc (-Real.pi) Real.pi, cellExponential (-mode) angle • field angle) at commutes
  change (∫ angle in Icc (-Real.pi) Real.pi, cellExponential (-mode) angle • mapping (field angle)) =
    mapping (∫ angle in Icc (-Real.pi) Real.pi, cellExponential (-mode) angle • field angle)
  simpa only [map_smul] using commutes

theorem angularCoefficient_sub_continuous {dimension : ℕ}
    (first second : ℝ → ComplexEuclidean dimension)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (mode : ℤ) :
    angularCoefficient (first - second) mode = angularCoefficient first mode - angularCoefficient second mode := by
  rw [sub_eq_add_neg, angularCoefficient_add_continuous first (-second) firstContinuous secondContinuous.neg]
  have negative : -second = (-1 : ℂ) • second := by ext angle; simp
  rw [negative, angularCoefficient_smul_continuous, neg_one_smul, sub_eq_add_neg]

theorem tangentialBoundaryCoefficient_formula (parameters : PhaseParameters)
    (field : ACore parameters 2) (mode : ℤ × ℤ) :
    originalBoundaryCoefficient parameters (tangentialBoundaryCore parameters field) mode =
      planarComponentMap 1 ((2 : ℂ)⁻¹ •
        (originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2) +
          originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2))) -
      planarComponentMap 0 ((2 * Complex.I : ℂ)⁻¹ •
        (originalBoundaryCoefficient parameters field (mode.1 - 1, mode.2) -
          originalBoundaryCoefficient parameters field (mode.1 + 1, mode.2))) := by
  let circle : CellCircle → ComplexEuclidean 2 :=
    fun angle => (field.val mode.2).value (boundaryDiskPoint angle)
  let lift : ℝ → ComplexEuclidean 2 := fun angle => circle (angle : CellCircle)
  have continuousLift : Continuous lift := (field.val mode.2).value.continuous.comp
    (boundaryDiskPoint_continuous.comp (AddCircle.continuous_mk' _))
  have cosine : Continuous (fun angle => (Real.cos angle : ℂ) • lift angle) :=
    (Complex.continuous_ofReal.comp Real.continuous_cos).smul continuousLift
  have sine : Continuous (fun angle => (Real.sin angle : ℂ) • lift angle) :=
    (Complex.continuous_ofReal.comp Real.continuous_sin).smul continuousLift
  have literal : (fun angle : ℝ => ((tangentialBoundaryCore parameters field).val mode.2).value
      (boundaryDiskPoint (angle : CellCircle))) =
      (fun angle : ℝ => planarComponentMap 1 ((Real.cos angle : ℂ) • lift angle)) -
        (fun angle : ℝ => planarComponentMap 0 ((Real.sin angle : ℂ) • lift angle)) := by
    funext angle
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    exact tangentialBoundaryCore_unit_circle parameters field mode.2 angle
  change fourierCoeff (fun angle : CellCircle =>
    ((tangentialBoundaryCore parameters field).val mode.2).value (boundaryDiskPoint angle)) mode.1 = _
  rw [← angularCoefficient_circle, literal, angularCoefficient_sub_continuous
    (fun angle : ℝ => planarComponentMap 1 ((Real.cos angle : ℂ) • lift angle))
    (fun angle : ℝ => planarComponentMap 0 ((Real.sin angle : ℂ) • lift angle))
    ((planarComponentMap 1).continuous.comp cosine) ((planarComponentMap 0).continuous.comp sine),
    angularCoefficient_valueMap _ _ cosine, angularCoefficient_valueMap _ _ sine,
    angularCoefficient_cos_mul _ continuousLift, angularCoefficient_sin_mul _ continuousLift]
  change planarComponentMap 1 ((2 : ℂ)⁻¹ •
      (angularCoefficient (fun angle => circle (angle : CellCircle)) (mode.1 - 1) +
        angularCoefficient (fun angle => circle (angle : CellCircle)) (mode.1 + 1))) -
    planarComponentMap 0 ((2 * Complex.I : ℂ)⁻¹ •
      (angularCoefficient (fun angle => circle (angle : CellCircle)) (mode.1 - 1) -
        angularCoefficient (fun angle => circle (angle : CellCircle)) (mode.1 + 1))) = _
  rw [angularCoefficient_circle, angularCoefficient_circle]
  rfl

theorem annularShiftScalar_boundaryWeight (parameters : PhaseParameters) (power : ℕ)
    (shift : ℤ) (mode : ℤ × ℤ) :
    annularShiftScalar power shift mode *
      (sourceBoundaryWeight parameters power (mode.1 - shift, mode.2) : ℂ) =
      (sourceBoundaryWeight parameters power mode : ℂ) := by
  unfold sourceBoundaryWeight
  push_cast
  rw [mul_left_comm, annularShiftScalar_mul_weight]

end Grad.SourceBoundaryTrace
