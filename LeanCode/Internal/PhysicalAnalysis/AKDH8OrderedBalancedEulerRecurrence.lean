import AKDH7ActualPhysicalRowsOriginalPhase

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate

/-- Ordered SR19 expressions. `false` labels A and `true` labels B.
Source jets and operator jets keep separate ranks. -/
inductive BalancedEulerExpr where
  | unknown
  | source (rank : ℕ)
  | apply (kind : Bool) (rank : ℕ) (argument : BalancedEulerExpr)
  | add (first second : BalancedEulerExpr)

/-- Every operator factor consumes its one tangential order in addition
to its Euler rank. The terminal source rank is counted exactly once. -/
def balancedExprCost : BalancedEulerExpr → ℕ :=
  BalancedEulerExpr.rec 0 id (fun _ rank _ previous => rank+1+previous)
    (fun _ _ first second => max first second)

def balancedExprDerivative : BalancedEulerExpr → BalancedEulerExpr :=
  BalancedEulerExpr.rec
    (.add (.apply false 0 .unknown) (.apply true 0 (.source 0)))
    (fun rank => .source (rank+1))
    (fun kind rank argument previous => .add (.apply kind (rank+1) argument) (.apply kind rank previous))
    (fun _ _ first second => .add first second)

def balancedEulerExpression (rank : ℕ) : BalancedEulerExpr :=
  Nat.rec .unknown (fun _ previous => balancedExprDerivative previous) rank

theorem balancedExprDerivative_cost (expression : BalancedEulerExpr) :
    balancedExprCost (balancedExprDerivative expression) ≤ balancedExprCost expression+1 := by
  induction expression with
  | unknown => decide
  | source rank => exact le_rfl
  | apply kind rank argument previous =>
      change max (rank+1+1+balancedExprCost argument)
        (rank+1+balancedExprCost (balancedExprDerivative argument)) ≤ rank+1+balancedExprCost argument+1
      omega
  | add first second firstBound secondBound =>
      change max (balancedExprCost (balancedExprDerivative first)) (balancedExprCost (balancedExprDerivative second)) ≤
        max (balancedExprCost first) (balancedExprCost second)+1
      omega

theorem balancedEulerExpression_cost (rank : ℕ) : balancedExprCost (balancedEulerExpression rank) ≤ rank := by
  induction rank with
  | zero => exact le_rfl
  | succ rank previous => exact (balancedExprDerivative_cost _).trans (Nat.add_le_add_right previous 1)

section Evaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def balancedExprValue (operators : Bool → ℕ → ℝ → E →L[ℝ] E)
    (unknown : ℝ → E) (source : ℕ → ℝ → E) : BalancedEulerExpr → ℝ → E :=
  BalancedEulerExpr.rec unknown source
    (fun kind rank _ previous point => operators kind rank point (previous point))
    (fun _ _ first second point => first point+second point)

/-- SR19 is differentiated before estimating it. The actual first-order
radial equation replaces only the terminal unknown; every product keeps
its order and every source differentiation remains explicit. -/
theorem balancedExprValue_hasDerivWithinAt (domain : Set ℝ)
    (operators : Bool → ℕ → ℝ → E →L[ℝ] E) (unknown : ℝ → E) (source : ℕ → ℝ → E)
    (radius : ℝ)
    (operatorDerivative : ∀ kind rank, HasDerivWithinAt (operators kind rank)
      (radius⁻¹ • operators kind (rank+1) radius) domain radius)
    (sourceDerivative : ∀ rank, HasDerivWithinAt (source rank)
      (radius⁻¹ • source (rank+1) radius) domain radius)
    (equation : HasDerivWithinAt unknown
      (radius⁻¹ • (operators false 0 radius (unknown radius)+operators true 0 radius (source 0 radius))) domain radius)
    (expression : BalancedEulerExpr) :
    HasDerivWithinAt (balancedExprValue operators unknown source expression)
      (radius⁻¹ • balancedExprValue operators unknown source (balancedExprDerivative expression) radius) domain radius := by
  induction expression with
  | unknown => exact equation
  | source rank => exact sourceDerivative rank
  | apply kind rank argument previous =>
      have result := actualBilinear_hasDerivWithinAt ((ContinuousLinearMap.apply ℝ E).flip)
        domain (operators kind rank) (balancedExprValue operators unknown source argument) radius _ _
        (operatorDerivative kind rank) previous
      apply result.congr_deriv
      change (radius⁻¹ • operators kind (rank+1) radius) (balancedExprValue operators unknown source argument radius)+
        operators kind rank radius (radius⁻¹ • balancedExprValue operators unknown source (balancedExprDerivative argument) radius) =
        radius⁻¹ • (operators kind (rank+1) radius (balancedExprValue operators unknown source argument radius)+
          operators kind rank radius (balancedExprValue operators unknown source (balancedExprDerivative argument) radius))
      rw [_root_.smul_apply,map_smul,smul_add]
  | add first second firstDerivative secondDerivative =>
      exact (firstDerivative.add secondDerivative).congr_deriv (smul_add _ _ _).symm

/-- Exact ordered expansion of genuine closed-collar Euler derivatives
of a first-order balanced solution, including one-sided endpoints. -/
theorem balancedEulerExpression_fidelity (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (nonzero : ∀ radius ∈ domain, radius ≠ 0)
    (operators : Bool → ℕ → ℝ → E →L[ℝ] E) (unknown : ℝ → E) (source : ℕ → ℝ → E)
    (operatorDerivative : ∀ kind rank radius, radius ∈ domain → HasDerivWithinAt (operators kind rank)
      (radius⁻¹ • operators kind (rank+1) radius) domain radius)
    (sourceDerivative : ∀ rank radius, radius ∈ domain → HasDerivWithinAt (source rank)
      (radius⁻¹ • source (rank+1) radius) domain radius)
    (equation : ∀ radius ∈ domain, HasDerivWithinAt unknown
      (radius⁻¹ • (operators false 0 radius (unknown radius)+operators true 0 radius (source 0 radius))) domain radius)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank unknown radius =
      balancedExprValue operators unknown source (balancedEulerExpression rank) radius :=
  vectorEulerWithinIteratedDerivative_tower domain unique nonzero
    (fun order => balancedExprValue operators unknown source (balancedEulerExpression order))
    (fun order point member => balancedExprValue_hasDerivWithinAt domain operators unknown source point
      (fun kind raw => operatorDerivative kind raw point member) (fun raw => sourceDerivative raw point member)
      (equation point member) (balancedEulerExpression order)) rank inside

end Evaluation
end Grad.OriginalCartesianTameEstimate
