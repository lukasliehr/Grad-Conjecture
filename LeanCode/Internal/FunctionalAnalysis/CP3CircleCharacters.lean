import CP2CollarCorrection

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open MeasureTheory

/-- Character shift under the Fourier coefficient: both sides are the
same circle integral, so no integrability hypothesis is needed. -/
theorem fourierCoeff_character_shift (k m : ℤ) (f : CellCircle → ℂ) :
    fourierCoeff (fun angle => fourier k angle * f angle) m =
      fourierCoeff f (m - k) := by
  unfold fourierCoeff
  have integrands : (fun angle : CellCircle =>
      fourier (-m) angle • (fourier k angle * f angle)) =
      fun angle => fourier (-(m - k)) angle • f angle := by
    funext angle
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← fourier_add,
      show -m + k = -(m - k) by ring]
  rw [integrands]

/-- Constant complex rescaling of a coefficient. -/
theorem fourierCoeff_const_mul (scalar : ℂ) (f : CellCircle → ℂ) (m : ℤ) :
    fourierCoeff (fun angle => scalar * f angle) m = scalar * fourierCoeff f m := by
  unfold fourierCoeff
  have rescaled : (∫ angle : CellCircle,
      fourier (-m) angle • (scalar • f angle) ∂AddCircle.haarAddCircle) =
      scalar • ∫ angle : CellCircle,
        fourier (-m) angle • f angle ∂AddCircle.haarAddCircle := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with angle
    rw [smul_comm]
  simpa [smul_eq_mul] using rescaled

/-- Coefficient additivity for continuous summands. -/
theorem fourierCoeff_add_continuous (f g : CellCircle → ℂ) (m : ℤ)
    (fContinuous : Continuous f) (gContinuous : Continuous g) :
    fourierCoeff (fun angle => f angle + g angle) m =
      fourierCoeff f m + fourierCoeff g m := by
  unfold fourierCoeff
  simp only [smul_add]
  apply integral_add
  · exact ((fourier _).continuous.smul fContinuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((fourier _).continuous.smul gContinuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The first boundary coordinate as the two first characters. -/
theorem circle_component_re (angle : CellCircle) :
    ((boundaryCirclePoint angle 0 : ℝ) : ℂ) =
      (fourier 1 angle + fourier (-1) angle) / 2 := by
  have componentValue : boundaryCirclePoint angle 0 =
      (AddCircle.toCircle angle : ℂ).re := rfl
  have fourierOne : (fourier 1 angle : ℂ) = (AddCircle.toCircle angle : ℂ) := by
    rw [fourier_apply, one_zsmul]
  have fourierNegOne : (fourier (-1) angle : ℂ) =
      (starRingEnd ℂ) (AddCircle.toCircle angle : ℂ) := by
    rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, fourier_neg, fourierOne]
  rw [componentValue, fourierOne, fourierNegOne, Complex.add_conj]
  push_cast
  ring

/-- The second boundary coordinate as the two first characters. -/
theorem circle_component_im (angle : CellCircle) :
    ((boundaryCirclePoint angle 1 : ℝ) : ℂ) =
      (fourier 1 angle - fourier (-1) angle) / (2 * Complex.I) := by
  have componentValue : boundaryCirclePoint angle 1 =
      (AddCircle.toCircle angle : ℂ).im := rfl
  have fourierOne : (fourier 1 angle : ℂ) = (AddCircle.toCircle angle : ℂ) := by
    rw [fourier_apply, one_zsmul]
  have fourierNegOne : (fourier (-1) angle : ℂ) =
      (starRingEnd ℂ) (AddCircle.toCircle angle : ℂ) := by
    rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, fourier_neg, fourierOne]
  rw [componentValue, fourierOne, fourierNegOne, Complex.sub_conj]
  field_simp
  push_cast
  ring

/-- Componentwise coefficients through the Euclidean projections. -/
theorem fourierCoeff_component {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) (m : ℤ) (index : Fin dimension) :
    fourierCoeff (fun angle : CellCircle =>
        ((field.1 cell).value (boundaryDiskPoint angle)) index) m =
      originalBoundaryCoefficient parameters field (m, cell) index := by
  unfold originalBoundaryCoefficient fourierCoeff
  have projected : (fun angle : CellCircle =>
      fourier (-m) angle • ((field.1 cell).value (boundaryDiskPoint angle)) index) =
      fun angle => EuclideanSpace.proj (𝕜 := ℂ) index
        (fourier (-m) angle • (field.1 cell).value (boundaryDiskPoint angle)) := by
    funext angle
    rw [map_smul]
    rfl
  rw [projected]
  rw [ContinuousLinearMap.integral_comp_comm]
  · rfl
  · exact ((fourier _).continuous.smul ((field.1 cell).value.continuous.comp
      boundaryDiskPoint_continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Grad.Cor18
