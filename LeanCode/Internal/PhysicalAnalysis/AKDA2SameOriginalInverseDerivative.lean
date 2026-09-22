import AKDA1FaithfulEulerMatrixObservation
import AKC5ReservedResolventDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2
open Grad.AnnularRadialSmoothness Grad.AnnularWeightedSmoothness

/-- Specialize the accepted exact resolvent derivative to an identity
reserve. The inverse derivative is proved from its actual inverse laws. -/
theorem sameInverse_hasDerivWithinAt {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (domain : Set ℝ) (forward inverse : ℝ → R) (slope : R) (base : ℝ)
    (right : forward base * inverse base = 1)
    (left : ∀ point ∈ domain, inverse point * forward point = 1)
    (continuous : ContinuousWithinAt inverse domain base)
    (derivative : HasDerivWithinAt forward slope domain base) :
    HasDerivWithinAt inverse (-(inverse base*slope)*inverse base) domain base := by
  have derived := reservedInverse_hasDerivWithinAt domain forward inverse 1 (inverse base) slope base
    right left (by simp) continuous (by simpa only [mul_one] using derivative)
  simpa only [mul_one] using derived

/-- The SAME original full-kernel negative-identity inverse in polynomial
coordinates. Its purpose here is fidelity; all quantitative estimates keep
fullKernelMoment at the original analytic width. -/
def actualPolynomialNegativeInverse {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius dimension dimension)
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernel radius) ≤ low) :
    ℝ → (CellL2 dimension →L[ℂ] CellL2 dimension) :=
  radialPolynomialAction parameters lower positive bounded
    (fun radius => fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius)
      (kernel radius) low (lowBound radius) small) 0

/-- Actual inverse differentiation on the closed original collar, including
one-sided endpoints. There is no inverse differentiability premise. -/
theorem actualPolynomialNegativeInverse_hasDerivWithinAt {dimension : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius dimension dimension)
    (smooth : SmoothPolynomialFamily parameters lower positive bounded kernel)
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernel radius) ≤ low)
    (base : ℝ) (inside : base ∈ Icc lower 1)
    (slope : CellL2 dimension →L[ℂ] CellL2 dimension)
    (derivative : HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded kernel 0)
      slope (Icc lower 1) base) :
    let inverse := actualPolynomialNegativeInverse parameters lower positive bounded kernel low small lowBound
    HasDerivWithinAt inverse (-(inverse base).comp slope |>.comp (inverse base)) (Icc lower 1) base := by
  let inverse := actualPolynomialNegativeInverse parameters lower positive bounded kernel low small lowBound
  let forward := fun point => radialPolynomialAction parameters lower positive bounded kernel 0 point -
    ContinuousLinearMap.id ℂ (CellL2 dimension)
  have laws (point : ℝ) : forward point * inverse point = 1 ∧ inverse point * forward point = 1 := by
    have original := polynomialKernelAction_inverse
      (radialKernelParameters parameters (collarRadius lower positive bounded point)) 0
      (kernel (collarRadius lower positive bounded point)) low (lowBound _) small
    simp only [fullKernelNegativeIdentityPerturbation,polynomialKernelAction_sub,polynomialKernelAction_identity] at original
    exact original
  have inverseSmooth := SmoothPolynomialFamily.negativeInverse smooth low small lowBound
  have derived : HasDerivWithinAt forward slope (Icc lower 1) base := by
    simpa only [Pi.sub_def] using derivative.sub_const (ContinuousLinearMap.id ℂ (CellL2 dimension))
  exact sameInverse_hasDerivWithinAt (Icc lower 1) forward inverse slope base (laws base).1
    (fun point _ => (laws point).2) ((inverseSmooth 0).continuousOn base inside) derived

end Grad.OriginalCartesianTameEstimate
