import SCS31PhysicalDividedSources

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.SourceCollarBulk Grad.FlatSourceProjection Grad.QuotientProjection Grad.AxisCore
open Grad.SourceBoundaryTrace

theorem coreDividedSourceCells_continuous (parameters : PhaseParameters) (L : ℝ)
    (source : SmoothQuotient parameters) (cell : ℤ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (component : Fin 3) :
    Continuous (coreDividedSourceCells parameters L source cell radius nonnegative bounded component) := by
  have pointContinuous : Continuous (fun angle => polarClosedPoint radius angle nonnegative bounded) :=
    (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have planar : Continuous (fun angle => radius⁻¹ • ((cartesianSourceVector source).val cell).value
      (polarClosedPoint radius angle nonnegative bounded)) :=
    (continuous_const : Continuous (fun _ : ℝ => radius⁻¹)).smul
      (((cartesianSourceVector source).val cell).value.continuous.comp pointContinuous)
  have fourth : Continuous (fun angle => radius⁻¹ • ((source 3).val cell).value
      (polarClosedPoint radius angle nonnegative bounded)) :=
    (continuous_const : Continuous (fun _ : ℝ => radius⁻¹)).smul
      (((source 3).val cell).value.continuous.comp pointContinuous)
  fin_cases component
  · exact radialProjection_continuous.clm_apply planar
  · exact tangentialProjection_continuous.clm_apply planar
  · exact (continuous_const : Continuous (fun _ : ℝ => (L : ℂ)⁻¹)).smul fourth

theorem physicalDividedSources_axialCoefficient (parameters : PhaseParameters) (L : ℝ)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (component : Fin 3) (polar : ℝ) (cell : ℤ) :
    angularCoefficient (fun axial => physicalDividedSources parameters L source radius nonnegative bounded
      component (polar, axial)) cell = coreDividedSourceCells parameters L source cell radius nonnegative bounded component polar := by
  have planar : Continuous (fun axial => radius⁻¹ • corePolarValue parameters (cartesianSourceVector source)
      radius nonnegative bounded (polar, axial)) :=
    (continuous_const : Continuous (fun _ : ℝ => radius⁻¹)).smul
      ((corePolarValue_continuous parameters (cartesianSourceVector source) radius nonnegative bounded).comp
        (continuous_const.prodMk continuous_id))
  fin_cases component
  · change angularCoefficient (fun axial => radialProjection polar (radius⁻¹ • corePolarValue parameters
      (cartesianSourceVector source) radius nonnegative bounded (polar, axial))) cell = _
    rw [angularCoefficient_valueMap _ _ planar, angularCoefficient_real_smul, corePolarValue_axialCoefficient]
    rfl
  · change angularCoefficient (fun axial => tangentialProjection polar (radius⁻¹ • corePolarValue parameters
      (cartesianSourceVector source) radius nonnegative bounded (polar, axial))) cell = _
    rw [angularCoefficient_valueMap _ _ planar, angularCoefficient_real_smul, corePolarValue_axialCoefficient]
    rfl
  · change angularCoefficient ((L : ℂ)⁻¹ • (fun axial => radius⁻¹ • corePolarValue parameters
      (source 3) radius nonnegative bounded (polar, axial))) cell = _
    rw [angularCoefficient_smul_continuous, angularCoefficient_real_smul, corePolarValue_axialCoefficient]
    rfl

end Grad.SourceCollarFullSource
