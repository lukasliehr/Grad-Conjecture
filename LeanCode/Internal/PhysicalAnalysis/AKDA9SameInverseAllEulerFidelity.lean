import AKDA8ActualEulerKernelOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness

/-- Ordered Euler kernel of the existing inverse. The unchanged inverse
is used at rank zero and in every higher-rank ordered factor. -/
def actualNegativeInverseEulerKernel {dimension : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (kernels : ℕ → RadialKernel parameters radius dimension dimension)
    (low : ℝ) (small : low < 1)
    (lowBound : fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels 0) ≤ low)
    (rank : ℕ) : RadialKernel parameters radius dimension dimension :=
  inverseEulerExprKernel
    (fullKernelNegativeIdentityInverse (radialKernelParameters parameters radius) (kernels 0) low lowBound small)
    (actualRawEulerKernel radius kernels) (inverseEulerExpression rank)

theorem actualNegativeInverseEulerKernel_action {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius dimension dimension)
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels 0 radius) ≤ low)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    polynomialKernelAction (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0
      (actualNegativeInverseEulerKernel parameters (collarRadius lower positive bounded radius)
        (fun raw => kernels raw (collarRadius lower positive bounded radius)) low small (lowBound _) rank) =
      inverseEulerExprValue
        (actualPolynomialNegativeInverse parameters lower positive bounded (kernels 0) low small lowBound radius)
        (fun raw => actualRawEulerJets (fun order => radialPolynomialAction parameters lower positive bounded (kernels order) 0) raw radius)
        (inverseEulerExpression rank) := by
  rw [actualNegativeInverseEulerKernel,inverseEulerExprKernel_action]
  congr 1
  funext raw
  exact actualRawEulerKernel_collar_action parameters lower positive bounded kernels raw radius inside

/-- Every ordered formula is the genuine Euler derivative of the literal
inverse entry on the original closed positive collar. The raw forward
derivative tower and its smoothness determine the inverse derivatives. -/
theorem actualNegativeInverseEulerKernel_hasDerivWithinAt {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius dimension dimension)
    (smooth : SmoothPolynomialFamily parameters lower positive bounded.le (kernels 0))
    (derivative : ∀ raw radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded.le (kernels raw) 0)
        (radialPolynomialAction parameters lower positive bounded.le (kernels (raw+1)) 0 radius) (Icc lower 1) radius)
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels 0 radius) ≤ low)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift input : ℤ × ℤ) :
    HasDerivWithinAt (fun point =>
      (actualNegativeInverseEulerKernel parameters (collarRadius lower positive bounded.le point)
        (fun raw => kernels raw (collarRadius lower positive bounded.le point)) low small (lowBound _) rank).entry shift input)
      (radius⁻¹ • (actualNegativeInverseEulerKernel parameters (collarRadius lower positive bounded.le radius)
        (fun raw => kernels raw (collarRadius lower positive bounded.le radius)) low small (lowBound _) (rank+1)).entry shift input)
      (Icc lower 1) radius := by
  let raw := fun order => radialPolynomialAction parameters lower positive bounded.le (kernels order) 0
  let inverse := actualPolynomialNegativeInverse parameters lower positive bounded.le (kernels 0) low small lowBound
  let forward := actualRawEulerJets raw
  have nonzero : ∀ point ∈ Icc lower 1, point ≠ 0 := fun point member => (positive.trans_le member.1).ne'
  have inverseDerivative : ∀ point, point ∈ Icc lower 1 → HasDerivWithinAt inverse
      (point⁻¹ • (-(inverse point*(forward 1 point*inverse point)))) (Icc lower 1) point := by
    intro point member
    have result := actualPolynomialNegativeInverse_hasDerivWithinAt parameters lower positive bounded.le
      (kernels 0) smooth low small lowBound point member (raw 1 point) (derivative 0 point member)
    change HasDerivWithinAt inverse (-(inverse point*raw 1 point)*inverse point) (Icc lower 1) point at result
    apply result.congr_deriv
    change -(inverse point*raw 1 point)*inverse point =
      point⁻¹ • (-(inverse point*((1 • (point^1 • raw 1 point)+0)*inverse point)))
    simp only [pow_one,one_smul,add_zero,mul_smul_comm,smul_mul_assoc,smul_neg,inv_smul_smul₀ (nonzero point member),neg_mul,mul_assoc]
  have forwardDerivative : ∀ order point, point ∈ Icc lower 1 →
      HasDerivWithinAt (forward (order+1)) (point⁻¹ • forward (order+2) point) (Icc lower 1) point := by
    intro order point member
    exact actualRawEulerJets_hasDerivWithinAt (Icc lower 1) raw point (nonzero point member)
      (fun raw => derivative raw point member) (order+1)
  let jets := fun order point => inverseEulerExprValue (inverse point) (fun raw => forward raw point) (inverseEulerExpression order)
  let observe := (fourierEntryObservation (source := dimension) (target := dimension)
    ((twoFrequencyTranslation shift).symm input) input).restrictScalars ℝ
  have observedDerivative : ∀ order point, point ∈ Icc lower 1 →
      HasDerivWithinAt (fun location => observe (jets order location))
        (point⁻¹ • observe (jets (order+1) point)) (Icc lower 1) point := by
    intro order point member
    have result := inverseEulerExpr_hasDerivWithinAt (Icc lower 1) inverse forward point
      (inverseDerivative point member) (fun raw => forwardDerivative raw point member) (inverseEulerExpression order)
    have mapped := observe.hasFDerivAt.comp_hasDerivWithinAt point result
    change HasDerivWithinAt (fun location => observe (jets order location))
      (observe (point⁻¹ • jets (order+1) point)) (Icc lower 1) point at mapped
    simpa only [map_smul] using mapped
  have same (order : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) :
      observe (jets order point) =
        (actualNegativeInverseEulerKernel parameters (collarRadius lower positive bounded.le point)
          (fun raw => kernels raw (collarRadius lower positive bounded.le point)) low small (lowBound _) order).entry shift input := by
    have kernel := congrArg (fun mapping => fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input mapping)
      (actualNegativeInverseEulerKernel_action parameters lower positive bounded.le kernels low small lowBound order point member)
    rw [fourierEntryObservation_kernel] at kernel
    exact kernel.symm
  have result := observedDerivative rank radius inside
  rw [same (rank+1) radius inside] at result
  apply result.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with point member
    exact (same rank point member).symm
  · exact (same rank radius inside).symm

/-- Every ordered formula is the genuine Euler derivative of the literal
inverse entry on the original closed positive collar. The raw forward
derivative tower and its smoothness determine the inverse derivatives. -/
theorem actualNegativeInverseEulerKernel_fidelity {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius dimension dimension)
    (smooth : SmoothPolynomialFamily parameters lower positive bounded.le (kernels 0))
    (derivative : ∀ raw radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded.le (kernels raw) 0)
        (radialPolynomialAction parameters lower positive bounded.le (kernels (raw+1)) 0 radius) (Icc lower 1) radius)
    (low : ℝ) (small : low < 1)
    (lowBound : ∀ radius, fullKernelMoment (radialKernelParameters parameters radius) 0 (kernels 0 radius) ≤ low)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift input : ℤ × ℤ) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank (fun point =>
      (fullKernelNegativeIdentityInverse (radialKernelParameters parameters (collarRadius lower positive bounded.le point))
        (kernels 0 (collarRadius lower positive bounded.le point)) low (lowBound _) small).entry shift input) radius =
      (actualNegativeInverseEulerKernel parameters (collarRadius lower positive bounded.le radius)
        (fun raw => kernels raw (collarRadius lower positive bounded.le radius)) low small (lowBound _) rank).entry shift input := by
  have nonzero : ∀ point ∈ Icc lower 1, point ≠ 0 := fun point member => (positive.trans_le member.1).ne'
  exact vectorEulerWithinIteratedDerivative_tower (Icc lower 1) (uniqueDiffOn_Icc bounded) nonzero
    (fun order point => (actualNegativeInverseEulerKernel parameters (collarRadius lower positive bounded.le point)
      (fun raw => kernels raw (collarRadius lower positive bounded.le point)) low small (lowBound _) order).entry shift input)
    (fun order point member => actualNegativeInverseEulerKernel_hasDerivWithinAt parameters lower positive bounded
      kernels smooth derivative low small lowBound order point member shift input) rank inside

end Grad.OriginalCartesianTameEstimate
