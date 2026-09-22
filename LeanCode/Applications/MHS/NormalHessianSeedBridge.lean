import PhysicalSimilarityRigidity
import Grad.GeometryClosure.Hessian
import Mathlib.Tactic.FinCases

noncomputable section

namespace Grad.MainAssembly.NormalHessianSeedBridge

open Grad.MainTarget
open Grad.MainAssembly.NormalHessianCovariance
open Grad.MainAssembly.PhysicalSimilarityRigidity
open Grad.MainAssembly.TensorAngleRigidity
open Grad.GeometryClosure
open Matrix

/-- The recovered G20 matrix and the main-assembly matrix are literally the
same trace-normalized shape. -/
theorem angleShape_eq_normalizedShape (rho angle : ℝ) :
    angleShape rho angle = normalizedShape rho angle := by
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [angleShape, normalizedShape] <;> ring

/-- Exact NG_R03 bridge: once the actual physical normal Hessian is identified
with the G18 algebraic Hessian, its negative is invertible, the inverse trace
is the positive number `a^2`, and its normalized inverse is the prescribed
angle shape. -/
theorem normalHessian_seed_shape
    (pressure : Vec → ℝ) (radius time a rho angle : ℝ)
    (aPositive : 0 < a) (rhoLower : -1 < rho) (rhoUpper : rho < 1)
    (normalHessianFormula :
      normalHessianMatrix pressure radius time =
        algebraicNormalHessian a (seedMatrix rho angle)) :
    IsUnit (-(normalHessianMatrix pressure radius time)).det ∧
      ((-(normalHessianMatrix pressure radius time))⁻¹).trace = a ^ 2 ∧
      0 < ((-(normalHessianMatrix pressure radius time))⁻¹).trace ∧
      normalizedInverseShape (normalHessianMatrix pressure radius time) =
        normalizedShape rho angle := by
  have seedInvertible : IsUnit (seedMatrix rho angle).det :=
    isUnit_iff_ne_zero.mpr
      (ne_of_gt (seed_det rhoLower rhoUpper angle).2)
  have inverseProducts := algebraic_negative_hessian_inverse_products
    a aPositive (seedMatrix rho angle) seedInvertible
  have negativeHessianInvertible :
      IsUnit (-(algebraicNormalHessian a (seedMatrix rho angle))).det := by
    apply isUnit_iff_ne_zero.mpr
    intro determinantZero
    have determinantProduct := congrArg Matrix.det inverseProducts.1
    rw [Matrix.det_mul, determinantZero, zero_mul] at determinantProduct
    norm_num at determinantProduct
  have inverseTrace := algebraic_negative_hessian_inverse_trace
    a aPositive (seedMatrix rho angle) seedInvertible
    (seed_trace rhoLower rhoUpper angle).2
  have normalizedShapeFormula :
      normalizedInverseShape (algebraicNormalHessian a (seedMatrix rho angle)) =
        normalizedShape rho angle := by
    change algebraicNormalizedShape a (seedMatrix rho angle) =
      normalizedShape rho angle
    rw [algebraic_seed_shape a aPositive rhoLower rhoUpper angle,
      angleShape_eq_normalizedShape]
  rw [normalHessianFormula]
  exact ⟨negativeHessianInvertible, inverseTrace.1, inverseTrace.2,
    normalizedShapeFormula⟩

/-- Construction-facing form: the exact G18 physical Hessian identity supplies
the complete prescribed-normal-shape input used by the NG_R17 bridge. -/
theorem hasPrescribedNormalShape_of_seedHessian
    (representative : Representative) (pressure : Vec → ℝ)
    (radius rho alpha delta parameter a : ℝ)
    (represents : ∀ point : Reference,
      pressure (representative.position point) = representative.pressure point)
    (aPositive : 0 < a) (rhoLower : -1 < rho) (rhoUpper : rho < 1)
    (normalHessianFormula : ∀ time,
      normalHessianMatrix pressure radius time =
        algebraicNormalHessian a
          (seedMatrix rho (HarmonicRigidity.alphaAngle alpha delta parameter time))) :
    HasPrescribedNormalShape representative radius rho
      (HarmonicRigidity.alphaAngle alpha delta parameter) := by
  refine ⟨pressure, represents, ?_⟩
  intro time
  have exactShape := normalHessian_seed_shape pressure radius time a rho
    (HarmonicRigidity.alphaAngle alpha delta parameter time)
    aPositive rhoLower rhoUpper (normalHessianFormula time)
  exact ⟨exactShape.1, exactShape.2.2.2⟩

end Grad.MainAssembly.NormalHessianSeedBridge
