import QO5EulerMean

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRadial Grad.AxisSplit Grad.AxisJet
open Grad.QuotientProjection Grad.PhysicalFamily Grad.GaugeCoefficients.Radial

variable {parameters : PhaseParameters}

/-- Multiplication by the literal squared radius, factored without division. -/
def radiusSquaredCore {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (starZMulCore parameters).comp (zMulCore parameters)

theorem radiusSquaredCore_value {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) (point : ClosedDisk) :
    ((radiusSquaredCore parameters field).val cell).value point =
      ‖point.val‖ ^ 2 • (field.val cell).value point := by
  change ((starZMulCore parameters (zMulCore parameters field)).val cell).value point = _
  rw [starZMulCore_jet, coordinateMultiplyJet_value, zMulCore_jet,
    coordinateMultiplyJet_value, smul_smul, ← Complex.coe_smul]
  congr 1
  simp only [signedComplexCoordinate, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one, mul_one, Complex.ofReal_add,
    Complex.ofReal_pow]
  ring_nf
  simp [Complex.I_sq]

theorem angularCore_radiusSquaredCore {dimension : ℕ} (mode : ℤ)
    (field : ACore parameters dimension) :
    angularCore parameters mode (radiusSquaredCore parameters field) =
      radiusSquaredCore parameters (angularCore parameters mode field) := by
  change angularCore parameters mode (starZMulCore parameters (zMulCore parameters field)) = _
  rw [angularCore_starZMulCore, angularCore_zMulCore]
  rw [show mode + 1 - 1 = mode by omega]
  rfl

/-- The actual radial correction exactly divides the averaged Euler/angular
product on the whole closed disk, including the axis. -/
theorem quotientDot_radial_identity (field : ACore parameters 3) :
    radiusSquaredCore parameters (quotientDotCurried parameters field field) =
      angularCore parameters 0 (dotOperation parameters (eulerCore parameters field)
        (rotationCore parameters field)) := by
  let source := angularCore parameters 0 (dotOperation parameters (eulerCore parameters field)
    (rotationCore parameters field))
  have radial : ∀ cell, Grad.NonlinearDivision.IsRotationInvariant (source.val cell) := by
    intro cell angle point
    have equality := angularClosedJet_rotation_value 0
      ((dotOperation parameters (eulerCore parameters field) (rotationCore parameters field)).val cell)
      angle point
    simpa only [source, angularCore_apply, Grad.NonlinearDivision.IsRotationInvariant,
      Grad.NonlinearDivision.rotatedPoint, rotatedPoint, physicalRotation_eq_orthogonal,
      planeRotationEquiv_apply, angularCharacter_zero_mode, one_smul] using equality
  have origin : ∀ cell, (source.val cell).value Grad.NonlinearDivision.closedOrigin = 0 := by
    intro cell
    change originValue (angularClosedJet 0
      ((dotOperation parameters (eulerCore parameters field) (rotationCore parameters field)).val cell)) = 0
    rw [angularJet_zero_originValue]
    exact pairProduct_originValue_zero_right physicalDotProduct (eulerCore parameters field)
      (rotationCore parameters field) (rotationCore_originValue field) cell
  have division := Grad.NonlinearDivision.actualCoreRadialDivision parameters source radial origin
  apply acore_ext
  intro cell point
  rw [radiusSquaredCore_value]
  exact (division.1 cell point).symm

end Grad.NonlinearRange
