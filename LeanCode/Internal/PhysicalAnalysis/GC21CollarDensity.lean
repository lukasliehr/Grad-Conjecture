import GC21Boundary

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.BoundaryTrace

/-- Exact AP2 integral, not a lambda-weighted comparison. -/
theorem apDensityIntegral {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (cell : ℤ) (field : ClosedJet dimension) :
    (∫ point in closedUnitDisk, cartesianDensityGlobal (scaledCellWeight L ell cell) grade
      (apWeightedJet sigma gamma ell cell field) point) =
      ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
  rw [cartesianDensityGlobal_integral, apRowLinear_norm_sq]
  rfl

/-- The fixed geometric collar bounds each inserted kappa-weighted
derivative by the exact original AP2 cell norm, uniformly in ell. -/
theorem apWeightedCollarIntegral {dimension grade order : ℕ} (L sigma gamma ell : ℝ)
    (cell : ℤ) (field : ClosedJet dimension) (upper : order ≤ grade) :
    scaledCellWeight L ell cell ^ (2 * (grade - order)) * collarIntegral (fun point =>
      ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension
        (apWeightedJet sigma gamma ell cell field))) point‖ ^ 2) ≤
      ((4 / 3 : ℝ) * collarOrderConstant order) *
        ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
  let weighted := apWeightedJet sigma gamma ell cell field
  let density := cartesianDensityGlobal (scaledCellWeight L ell cell) grade weighted
  have densityContinuous : Continuous density := cartesianDensityGlobal_continuous _ _ _
  have derivativeContinuous : Continuous (fun point =>
      ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension weighted)) point‖ ^ 2) :=
    (((collarField_smooth (smoothClosedExtension_smooth weighted)).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm.pow 2)
  have pointwise : ∀ point ∈ collarRectangle,
      scaledCellWeight L ell cell ^ (2 * (grade - order)) *
        ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension weighted)) point‖ ^ 2 ≤
      collarOrderConstant order * density (collarPlane point) := by
    intro point inside
    have raw := weighted_collarDerivative_sq_le_density (scaledCellWeight L ell cell)
      (scaledCellWeight_one_le L ell cell) upper weighted point inside
    apply raw.trans_eq
    exact congrArg (fun value => collarOrderConstant order * value)
      (cartesianDensityGlobal_closed (scaledCellWeight L ell cell) grade weighted
        ⟨collarPlane point, (collarPlane_radius inside).2⟩).symm
  have comparison := collarIntegral_mono
    (fun point => scaledCellWeight L ell cell ^ (2 * (grade - order)) *
      ‖iteratedFDeriv ℝ order (collarField (smoothClosedExtension weighted)) point‖ ^ 2)
    (fun point => collarOrderConstant order * density (collarPlane point))
    (continuous_const.mul derivativeContinuous)
    (continuous_const.mul (densityContinuous.comp collarPlane_smooth.continuous)) pointwise
  rw [collarIntegral_const_mul, collarIntegral_const_mul] at comparison
  have polarBound := collar_integral_le_disk density densityContinuous (fun point =>
    cartesianPointDensity_nonnegative _ (scaledCellWeight_nonnegative L ell cell) _ _ _)
  have diskIntegral : (∫ point in closedUnitDisk, density point) =
      ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 :=
    apDensityIntegral L sigma gamma ell cell field
  rw [diskIntegral] at polarBound
  exact comparison.trans (by
    simpa only [collarIntegral, mul_assoc, mul_left_comm (collarOrderConstant order)] using
      mul_le_mul_of_nonneg_left polarBound (collarOrderConstant_nonnegative order))

end Grad.GaugeCoefficients.Physical.WeightedTrace
