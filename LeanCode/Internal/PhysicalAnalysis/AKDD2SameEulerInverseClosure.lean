import AKDD1ActualKernelEulerTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness

/-- Same negative-identity inverse applied to an already differentiated
actual kernel tower; no conversion back to ordinary radial jets is needed. -/
def sameNegativeInverseEulerKernel {dimension : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius dimension dimension)
    (low : ℝ) (small : low < 1)
    (lowBound : fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels 0) ≤ low)
    (rank : ℕ) : RadialKernel parameters radius dimension dimension :=
  inverseEulerExprKernel
    (fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernels 0) low lowBound small)
    kernels (inverseEulerExpression rank)

theorem sameNegativeInverseEulerKernel_zero {dimension : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius dimension dimension)
    (low : ℝ) (small : low < 1)
    (lowBound : fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels 0) ≤ low) :
    sameNegativeInverseEulerKernel parameters radius kernels low small lowBound 0 =
      fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernels 0) low lowBound small := rfl

/-- Closure under the original inverse: genuine operator derivatives,
ordered factors and all original kernel entries are retained. -/
theorem KernelEulerDerivativeTower.negativeInverse {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius dimension dimension)
    (tower : KernelEulerDerivativeTower parameters lower positive bounded kernels)
    (smooth : SmoothPolynomialFamily parameters lower positive bounded (kernels 0))
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels 0 radius) ≤ low) :
    KernelEulerDerivativeTower parameters lower positive bounded
      (fun rank radius => sameNegativeInverseEulerKernel parameters radius (fun order => kernels order radius) low small (lowBound radius) rank) := by
  let forward := fun order => radialPolynomialAction parameters lower positive bounded (kernels order) 0
  let inverse := actualPolynomialNegativeInverse parameters lower positive bounded (kernels 0) low small lowBound
  have inverseDerivative : ∀ point, point ∈ Icc lower 1 → HasDerivWithinAt inverse
      (point⁻¹ • (-(inverse point*(forward 1 point*inverse point)))) (Icc lower 1) point := by
    intro point member
    have result := actualPolynomialNegativeInverse_hasDerivWithinAt parameters lower positive bounded
      (kernels 0) smooth low small lowBound point member (point⁻¹ • forward 1 point) (tower 0 point member)
    change HasDerivWithinAt inverse (-(inverse point*(point⁻¹ • forward 1 point))*inverse point) (Icc lower 1) point at result
    apply result.congr_deriv
    simp only [mul_smul_comm,smul_mul_assoc,smul_neg,neg_mul,mul_assoc]
  have same (order : ℕ) (point : ℝ) :
      radialPolynomialAction parameters lower positive bounded
        (fun radius => sameNegativeInverseEulerKernel parameters radius (fun raw => kernels raw radius) low small (lowBound radius) order) 0 point =
      inverseEulerExprValue (inverse point) (fun raw => forward raw point) (inverseEulerExpression order) :=
    inverseEulerExprKernel_action _ _ _ _
  intro rank radius inside
  have result := inverseEulerExpr_hasDerivWithinAt (Icc lower 1) inverse forward radius
    (inverseDerivative radius inside) (fun raw => tower (raw+1) radius inside) (inverseEulerExpression rank)
  change HasDerivWithinAt (fun point => inverseEulerExprValue (inverse point) (fun raw => forward raw point) (inverseEulerExpression rank))
    (radius⁻¹ • inverseEulerExprValue (inverse radius) (fun raw => forward raw radius) (inverseEulerExpression (rank+1))) (Icc lower 1) radius at result
  rw [← same (rank+1) radius] at result
  apply result.congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall (same rank)
  · exact same rank radius

end Grad.OriginalCartesianTameEstimate
