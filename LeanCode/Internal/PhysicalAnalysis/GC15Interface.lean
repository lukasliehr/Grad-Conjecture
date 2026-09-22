import GC14ActualFrameConsumer
import OriginalOneHighAllocation
import GC12SlotProduct

noncomputable section

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Allocation

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.NonlinearProduct

/-- The original physical B grade, including both finite state parameters. -/
def physicalBudget (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) (grade : ℕ) : ℝ :=
  originalGradeNorm grade field + |rho| + |epsilon|

/-- All grades of one completed full-cell coefficient. Coherence below
identifies the same closed derivative; it is not an analytic estimate. -/
abbrev CoefficientFamily (L sigma gamma ell : ℝ) (input output : ℕ) :=
  (grade : ℕ) → Coefficient L sigma gamma ell grade input output

def FamilyCoherent {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) : Prop :=
  ∀ (firstGrade secondGrade : ℕ) (first : DerivativeIndex firstGrade)
    (second : DerivativeIndex secondGrade),
    derivativeMultiIndex first = derivativeMultiIndex second →
      ∀ (cell : ℤ) (point : ClosedDisk),
        coefficientDerivative (family firstGrade) cell first point =
          coefficientDerivative (family secondGrade) cell second point

/-- A finite typed expression. Product order and every intermediate physical
dimension are retained. Fixed matrix operations are sums of such products. -/
inductive CoefficientExpression : ℕ → ℕ → Type
  | atom (input output label : ℕ) : CoefficientExpression input output
  | add {input output : ℕ} : CoefficientExpression input output →
      CoefficientExpression input output → CoefficientExpression input output
  | smul {input output : ℕ} (scalar : ℂ) : CoefficientExpression input output →
      CoefficientExpression input output
  | comp {input middle output : ℕ} : CoefficientExpression middle output →
      CoefficientExpression input middle → CoefficientExpression input output

abbrev CoefficientAssignment (L sigma gamma ell : ℝ) :=
  (input output label : ℕ) → CoefficientFamily L sigma gamma ell input output

def AssignmentCoherent {L sigma gamma ell : ℝ}
    (assignment : CoefficientAssignment L sigma gamma ell) : Prop :=
  ∀ input output label, FamilyCoherent (assignment input output label)

def evaluateExpression {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (assignment : CoefficientAssignment L sigma gamma ell) (grade : ℕ)
    {input output : ℕ} (expression : CoefficientExpression input output) :
    Coefficient L sigma gamma ell grade input output := by
  induction expression with
  | atom input output label => exact assignment input output label grade
  | add _ _ firstValue secondValue => exact firstValue + secondValue
  | smul scalar _ value => exact scalar • value
  | comp _ _ outerValue innerValue =>
    exact coefficientComposition admissible grade outerValue innerValue

/-- Constants indexed by the literal atom and grade. They are quantified
before ell and the physical state in the public finite-expression theorem. -/
abbrev AtomConstants := ℕ → ℕ → ℕ → ℕ → ℝ

def AtomBounds {L ell : ℝ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset : ℕ)
    (actual reference : CoefficientAssignment L parameters.sigma0 parameters.gamma ell)
    (fixedConstants deviationConstants : AtomConstants) : Prop :=
  ∀ input output label grade,
    ‖reference input output label grade‖ ≤ fixedConstants input output label grade ∧
      ‖actual input output label grade - reference input output label grade‖ ≤
        deviationConstants input output label grade *
          physicalBudget parameters field rho epsilon (offset + grade)

/-- AQ2 on the literal physical state, including endpoints and zero low norms. -/
def PhysicalInterpolationGoal : Prop :=
  ∀ offset grade : ℕ, 0 < grade → ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (parameters : PhaseParameters) (field : ACore parameters 3)
      (rho epsilon : ℝ) (order : ℕ), order ≤ grade →
      physicalBudget parameters field rho epsilon (offset + order) ≤ constant *
        (physicalBudget parameters field rho epsilon offset ^ (1 - (order : ℝ) / grade) *
          physicalBudget parameters field rho epsilon (offset + grade) ^ ((order : ℝ) / grade))

/-- AQ8: every spatial derivative and polynomial cell moment is allocated
before taking norms. No two unrestricted high coefficient norms occur. -/
def AllocatedCompositionGoal : Prop :=
  ∀ grade : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (L sigma gamma ell : ℝ) (admissible : Admissible L sigma gamma ell)
      (input middle output : ℕ)
      (outer : CoefficientFamily L sigma gamma ell middle output)
      (inner : CoefficientFamily L sigma gamma ell input middle),
      FamilyCoherent outer → FamilyCoherent inner →
      ‖coefficientComposition admissible grade (outer grade) (inner grade)‖ ≤
        constant * ∑ order : Fin (grade + 1), ‖outer order.val‖ * ‖inner (grade - order.val)‖

/-- CT_GC15: every fixed finite typed sum/product has the literal product
circle value, one high original B grade, and only a bounded low B offset.
The constant is independent of ell, the physical state and all atom values. -/
def FiniteCoefficientAllocationGoal : Prop :=
  ∀ (offset grade : ℕ) (lowBound : ℝ), 0 ≤ lowBound →
    ∀ (input output : ℕ) (expression : CoefficientExpression input output)
      (fixedConstants deviationConstants : AtomConstants),
      (∀ input output label grade, 0 ≤ fixedConstants input output label grade) →
      (∀ input output label grade, 0 ≤ deviationConstants input output label grade) →
      ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (parameters : PhaseParameters) (L ell : ℝ)
          (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
          (field : ACore parameters 3) (rho epsilon : ℝ)
          (actual reference : CoefficientAssignment L parameters.sigma0 parameters.gamma ell),
          AssignmentCoherent actual → AssignmentCoherent reference →
          physicalBudget parameters field rho epsilon offset ≤ lowBound →
          AtomBounds parameters field rho epsilon offset actual reference fixedConstants deviationConstants →
          ‖evaluateExpression admissible actual grade expression -
              evaluateExpression admissible reference grade expression‖ ≤
            constant * physicalBudget parameters field rho epsilon (offset + grade)

def BlockGoal : Prop :=
  PhysicalInterpolationGoal ∧ AllocatedCompositionGoal ∧ FiniteCoefficientAllocationGoal

end Grad.GaugeCoefficients.Physical.Allocation
