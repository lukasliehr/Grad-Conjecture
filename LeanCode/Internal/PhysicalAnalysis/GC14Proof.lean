import GC14ValueAdapters
import OriginalEvaluationProof

noncomputable section

namespace Grad.GaugeCoefficients.Physical

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

/-- Exact AP18 original-coefficient adapter.  The coefficient is constructed
in the existing completed original-width space, and every derivative is the
literal rescaled original coefficient derivative.  No physical frame is
postulated here; its later state-dependent construction remains separate. -/
def AP18Goal : Prop :=
  ∀ (parameters : PhaseParameters) (L ell : ℝ)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (dimension inputDimension outputDimension grade : ℕ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : GradeCore parameters dimension (grade + 3)),
    ‖originalCoefficient parameters L ell grade mapping field.toCore‖ ≤
        originalCoefficientConstant parameters grade * ‖mapping‖ * ‖field‖ ∧
      (∀ (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
        coefficientDerivative (originalCoefficient parameters L ell grade mapping field.toCore)
            cell index point = (ell ^ derivativeOrder index : ℂ) • mapping
          (closedMultiDerivative (field.toCore.1 cell) (derivativeMultiIndex index)
            (physicalScaledPoint ell admissible.2.2.2.1.le
              (admissible.2.2.2.2.trans (min_le_left _ _)) point)))

theorem ap18Goal : AP18Goal := by
  intro parameters L ell admissible dimension inputDimension outputDimension grade mapping field
  refine ⟨originalCoefficient_norm_bound parameters admissible mapping field, ?_⟩
  intro cell index point
  rw [originalCoefficient_derivative parameters admissible mapping field.toCore cell index point,
    radialPoint_eq_physicalScaledPoint]

/-- Coherent original-coefficient repair boundary: AP18 together with literal
NG_P01 reconstruction, reality, periodicity, and the original `j+3` norm. -/
theorem originalPhysicalAdapterBlock : AP18Goal ∧ OriginalPhysicalEvaluationGoal :=
  ⟨ap18Goal, originalPhysicalEvaluationBlock⟩

end Grad.GaugeCoefficients.Physical
