import SCS41OriginalPolarPoint

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.QuotientProjection Grad.FlatSourceProjection

def originalCorrectionNumerator (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (source : SmoothQuotient parameters) (radius : ℝ) (bounded : |radius| ≤ 1) (axial polar : ℝ) : ℂ :=
  let coefficients := actualPhysicalKappaSlice parameters L epsilon field radius bounded axial
  let sourceSlice := actualCartesianSourceSlice (spinToCartesian source) radius bounded axial
  coefficients polar 0 * Grad.Constraints.polarRadialComponent polar (sourceSlice.planar polar) +
    coefficients polar 1 * Grad.Constraints.polarTangentialComponent polar (sourceSlice.planar polar) -
    coefficients polar 2 * (sourceSlice.scalarH polar / (L : ℂ))

/-- The separated reference contribution is exactly the circular -F0/r;
all cofactor entries and the source are evaluated at the same physical point. -/
theorem physicalCorrection_literal (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (polar axial : ℝ) :
    physicalCorrection parameters L epsilon field source radius nonnegative bounded (polar, axial) 0 =
      originalCorrectionNumerator parameters L epsilon field source radius
        (by rwa [abs_of_nonneg nonnegative]) axial polar / (radius : ℂ) := by
  unfold physicalCorrection
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]
  change physicalKappaDeviation parameters L epsilon field radius nonnegative bounded 0 (polar, axial) *
      radialProjection polar (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar, axial)) 0 +
    physicalKappaDeviation parameters L epsilon field radius nonnegative bounded 1 (polar, axial) *
      tangentialProjection polar (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar, axial)) 0 -
    physicalKappaDeviation parameters L epsilon field radius nonnegative bounded 2 (polar, axial) *
      ((L : ℂ)⁻¹ * (radius⁻¹ • corePolarValue parameters (source 3) radius nonnegative bounded (polar, axial) 0)) -
    tangentialProjection polar (radius⁻¹ • corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded (polar, axial)) 0 = _
  simp only [radialProjection_component, tangentialProjection_component]
  dsimp only [physicalKappaDeviation, corePolarValue]
  simp_rw [divisionPolarPoint_eq_original]
  change
    (actualPhysicalKappaSlice parameters L epsilon field radius _ axial polar 0 - 0) *
      Grad.Constraints.polarRadialComponent polar (radius⁻¹ •
        (actualCartesianSourceSlice (spinToCartesian source) radius _ axial).planar polar) +
    (actualPhysicalKappaSlice parameters L epsilon field radius _ axial polar 1 - -1) *
      Grad.Constraints.polarTangentialComponent polar (radius⁻¹ •
        (actualCartesianSourceSlice (spinToCartesian source) radius _ axial).planar polar) -
    (actualPhysicalKappaSlice parameters L epsilon field radius _ axial polar 2 - 0) *
      ((L : ℂ)⁻¹ * (radius⁻¹ • (actualCartesianSourceSlice (spinToCartesian source) radius _ axial).scalarH polar)) -
    Grad.Constraints.polarTangentialComponent polar (radius⁻¹ •
        (actualCartesianSourceSlice (spinToCartesian source) radius _ axial).planar polar) = _
  simp only [originalCorrectionNumerator, Grad.Constraints.polarRadialComponent,
    Grad.Constraints.polarTangentialComponent, PiLp.smul_apply, Complex.real_smul,
    Complex.ofReal_inv, div_eq_mul_inv]
  ring

end Grad.SourceCollarFullSource
