import AKDA4ActualInverseKernelEntryDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness

/-- Ordered differentiation of an inverse keeps every primitive factor.
A forward index denotes a strictly positive Euler rank, index+1. -/
inductive InverseEulerExpr where
  | inverse : InverseEulerExpr
  | forward : ℕ → InverseEulerExpr
  | add : InverseEulerExpr → InverseEulerExpr → InverseEulerExpr
  | mul : InverseEulerExpr → InverseEulerExpr → InverseEulerExpr
  | neg : InverseEulerExpr → InverseEulerExpr

def inverseEulerExprDegree : InverseEulerExpr → ℕ :=
  InverseEulerExpr.rec 0 (fun rank => rank+1)
    (fun _ _ first second => max first second) (fun _ _ first second => first+second) (fun _ previous => previous)

def inverseEulerExprStep : InverseEulerExpr → InverseEulerExpr :=
  InverseEulerExpr.rec (.neg (.mul .inverse (.mul (.forward 0) .inverse))) (fun rank => .forward (rank+1))
    (fun _ _ first second => .add first second)
    (fun first second firstDerivative secondDerivative =>
      .add (.mul firstDerivative second) (.mul first secondDerivative)) (fun _ previous => .neg previous)

def inverseEulerExpression (rank : ℕ) : InverseEulerExpr :=
  Nat.rec .inverse (fun _ previous => inverseEulerExprStep previous) rank

theorem inverseEulerExprStep_degree (expression : InverseEulerExpr) :
    inverseEulerExprDegree (inverseEulerExprStep expression) ≤ inverseEulerExprDegree expression+1 := by
  induction expression with
  | inverse => exact le_rfl
  | forward rank => exact le_rfl
  | add first second firstBound secondBound =>
      change max (inverseEulerExprDegree (inverseEulerExprStep first))
        (inverseEulerExprDegree (inverseEulerExprStep second)) ≤
          max (inverseEulerExprDegree first) (inverseEulerExprDegree second)+1
      omega
  | mul first second firstBound secondBound =>
      change max (inverseEulerExprDegree (inverseEulerExprStep first)+inverseEulerExprDegree second)
        (inverseEulerExprDegree first+inverseEulerExprDegree (inverseEulerExprStep second)) ≤
          inverseEulerExprDegree first+inverseEulerExprDegree second+1
      omega
  | neg expression previous => exact previous

theorem inverseEulerExpression_degree (rank : ℕ) : inverseEulerExprDegree (inverseEulerExpression rank) ≤ rank := by
  induction rank with
  | zero => exact le_rfl
  | succ rank previous =>
      change inverseEulerExprDegree (inverseEulerExprStep (inverseEulerExpression rank)) ≤ rank+1
      exact (inverseEulerExprStep_degree _).trans (Nat.add_le_add_right previous 1)

section Evaluation
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

def inverseEulerExprValue (inverse : R) (forward : ℕ → R) : InverseEulerExpr → R :=
  InverseEulerExpr.rec inverse (fun rank => forward (rank+1))
    (fun _ _ first second => first+second) (fun _ _ first second => first*second) (fun _ previous => -previous)

/-- This is an actual derivative statement for the ordered expression.
The primitive and SAME inverse derivative laws are its only inputs. -/
theorem inverseEulerExpr_hasDerivWithinAt (domain : Set ℝ) (inverse : ℝ → R) (forward : ℕ → ℝ → R)
    (base : ℝ)
    (inverseDerivative : HasDerivWithinAt inverse
      (base⁻¹ • (-(inverse base*(forward 1 base*inverse base)))) domain base)
    (forwardDerivative : ∀ rank, HasDerivWithinAt (forward (rank+1))
      (base⁻¹ • forward (rank+2) base) domain base)
    (expression : InverseEulerExpr) :
    HasDerivWithinAt (fun point => inverseEulerExprValue (inverse point) (fun rank => forward rank point) expression)
      (base⁻¹ • inverseEulerExprValue (inverse base) (fun rank => forward rank base) (inverseEulerExprStep expression))
      domain base := by
  induction expression with
  | inverse => exact inverseDerivative
  | forward rank => exact forwardDerivative rank
  | add first second firstDerivative secondDerivative =>
      change HasDerivWithinAt (fun point => inverseEulerExprValue (inverse point) (fun rank => forward rank point) first +
        inverseEulerExprValue (inverse point) (fun rank => forward rank point) second)
        (base⁻¹ • (inverseEulerExprValue (inverse base) (fun rank => forward rank base) (inverseEulerExprStep first) +
          inverseEulerExprValue (inverse base) (fun rank => forward rank base) (inverseEulerExprStep second))) domain base
      simpa only [Pi.add_def,smul_add] using firstDerivative.add secondDerivative
  | mul first second firstDerivative secondDerivative =>
      change HasDerivWithinAt (fun point => inverseEulerExprValue (inverse point) (fun rank => forward rank point) first *
        inverseEulerExprValue (inverse point) (fun rank => forward rank point) second)
        (base⁻¹ • (inverseEulerExprValue (inverse base) (fun rank => forward rank base) (inverseEulerExprStep first) *
          inverseEulerExprValue (inverse base) (fun rank => forward rank base) second +
          inverseEulerExprValue (inverse base) (fun rank => forward rank base) first *
            inverseEulerExprValue (inverse base) (fun rank => forward rank base) (inverseEulerExprStep second))) domain base
      simpa only [Pi.mul_def,smul_add,smul_mul_assoc,mul_smul_comm] using firstDerivative.mul secondDerivative
  | neg expression previous =>
      change HasDerivWithinAt (fun point => -inverseEulerExprValue (inverse point) (fun rank => forward rank point) expression)
        (base⁻¹ • -inverseEulerExprValue (inverse base) (fun rank => forward rank base) (inverseEulerExprStep expression)) domain base
      rw [smul_neg]
      exact previous.neg

end Evaluation

def inverseEulerExprKernel {dimension : ℕ} {parameters : PhaseParameters}
    (inverse : FullTwoFrequencyKernel parameters dimension dimension)
    (forward : ℕ → FullTwoFrequencyKernel parameters dimension dimension) :
    InverseEulerExpr → FullTwoFrequencyKernel parameters dimension dimension :=
  InverseEulerExpr.rec inverse (fun rank => forward (rank+1))
    (fun _ _ first second => fullKernelAdd first second)
    (fun _ _ first second => fullKernelComposition first second) (fun _ previous => fullKernelNeg previous)

/-- Literal full-kernel evaluation agrees with the ordered operator value. -/
theorem inverseEulerExprKernel_action {dimension : ℕ} (parameters : PhaseParameters)
    (inverse : FullTwoFrequencyKernel parameters dimension dimension)
    (forward : ℕ → FullTwoFrequencyKernel parameters dimension dimension) (expression : InverseEulerExpr) :
    polynomialKernelAction parameters 0 (inverseEulerExprKernel inverse forward expression) =
      inverseEulerExprValue (polynomialKernelAction parameters 0 inverse)
        (fun rank => polynomialKernelAction parameters 0 (forward rank)) expression := by
  induction expression with
  | inverse => rfl
  | forward rank => rfl
  | add first second firstSame secondSame =>
      change polynomialKernelAction parameters 0 (fullKernelAdd (inverseEulerExprKernel inverse forward first)
        (inverseEulerExprKernel inverse forward second)) = _
      rw [polynomialKernelAction_add,firstSame,secondSame]
      rfl
  | mul first second firstSame secondSame =>
      change polynomialKernelAction parameters 0 (fullKernelComposition (inverseEulerExprKernel inverse forward first)
        (inverseEulerExprKernel inverse forward second)) = _
      rw [polynomialKernelAction_comp,firstSame,secondSame]
      rfl
  | neg expression previous =>
      change polynomialKernelAction parameters 0 (fullKernelNeg (inverseEulerExprKernel inverse forward expression)) = _
      rw [polynomialKernelAction_neg,previous]
      rfl

end Grad.OriginalCartesianTameEstimate
