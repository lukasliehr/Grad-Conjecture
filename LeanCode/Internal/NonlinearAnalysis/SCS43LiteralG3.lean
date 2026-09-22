import SCS42LiteralCorrection

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.QuotientProjection Grad.FlatSourceProjection
open Grad.BoundaryTrace Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Allocation

theorem removePolarMean_component (field : ℝ × ℝ → ComplexEuclidean 1)
    (continuousField : Continuous field) (periodic : ∀ axial, Function.Periodic (fun polar => field (polar, axial)) (2 * Real.pi))
    (polar axial : ℝ) :
    removePolarMean field (polar, axial) 0 = sourceAngularMeanFree (fun angle => field (angle, axial) 0) polar := by
  unfold removePolarMean sourceAngularMeanFree
  rw [PiLp.sub_apply]
  change field (polar, axial) 0 - angularCoefficient (fun theta => field (theta, axial)) 0 0 = _
  rw [angularCoefficient_component (fun theta => field (theta, axial))
    (continuousField.comp (continuous_id.prodMk continuous_const)) 0 0]
  congr 1
  exact (sourceAngularAverage_eq_coefficient (fun angle => field (angle, axial) 0)
    (fun angle => congrArg (fun value : ComplexEuclidean 1 => value 0) (periodic axial angle))).symm

theorem sourceAngularMeanFree_div (field : ℝ → ℂ) (scalar : ℂ) (angle : ℝ) :
    sourceAngularMeanFree (fun theta => field theta / scalar) angle = sourceAngularMeanFree field angle / scalar := by
  unfold sourceAngularMeanFree
  rw [sourceAngularAverage_div, sub_div]

/-- Exact BS30 physical G3, at the original physical radius and point.
The angular projection is after every cofactor product, with its circular
term retained. No shell scale or altered source datum enters the formula. -/
theorem physicalG3_literal (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (polar axial : ℝ) :
    physicalG3 parameters L epsilon field source radius nonnegative bounded (polar, axial) 0 =
      (actualAnnularBulkSource parameters L epsilon field radius (by rwa [abs_of_nonneg nonnegative])
        axial (spinToCartesian source)).G3 polar := by
  have numerator : (fun theta => physicalCorrection parameters L epsilon field source radius nonnegative bounded (theta, axial) 0) =
      (fun theta => originalCorrectionNumerator parameters L epsilon field source radius
        (by rwa [abs_of_nonneg nonnegative]) axial theta / (radius : ℂ)) :=
    funext (fun theta => physicalCorrection_literal parameters L epsilon field source radius nonnegative bounded theta axial)
  unfold physicalG3
  rw [PiLp.add_apply, PiLp.smul_apply, removePolarMean_component _
    (physicalCorrection_continuous parameters L rho epsilon field small source radius nonnegative bounded)
    (physicalCorrection_polar_periodic parameters L rho epsilon field small source radius nonnegative bounded),
    numerator, sourceAngularMeanFree_div]
  change (L : ℂ)⁻¹ * corePolarValue parameters (source 2) radius nonnegative bounded (polar, axial) 0 +
      sourceAngularMeanFree (originalCorrectionNumerator parameters L epsilon field source radius _ axial) polar / (radius : ℂ) = _
  change (L : ℂ)⁻¹ * corePolarValue parameters (source 2) radius nonnegative bounded (polar, axial) 0 +
      sourceAngularMeanFree (originalCorrectionNumerator parameters L epsilon field source radius _ axial) polar / (radius : ℂ) =
    (actualCartesianSourceSlice (spinToCartesian source) radius _ axial).scalarG polar / (L : ℂ) +
      sourceAngularMeanFree (originalCorrectionNumerator parameters L epsilon field source radius _ axial) polar / (radius : ℂ)
  congr 1
  unfold corePolarValue
  rw [divisionPolarPoint_eq_original]
  change (L : ℂ)⁻¹ * sourceCoreValue (source 2) (Grad.Constraints.polarClosedPoint radius _ polar) axial 0 =
    sourceCoreValue (source 2) (Grad.Constraints.polarClosedPoint radius _ polar) axial 0 / (L : ℂ)
  exact (div_eq_inv_mul _ _).symm

end Grad.SourceCollarFullSource
