import GC14ScaledBound

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set
open scoped BigOperators ENNReal ContDiff Topology

namespace Grad.GaugeCoefficients.Physical

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

local instance {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ} :
    CompleteSpace (Coefficient L sigma gamma ell grade inputDimension outputDimension) := by
  unfold Coefficient
  infer_instance

def originalCoefficientCell {dimension inputDimension outputDimension : ℕ}
    (parameters : PhaseParameters) (L ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (cell : ℤ) :
    Coefficient L parameters.sigma0 parameters.gamma ell grade inputDimension outputDimension :=
  coreInclusion L parameters.sigma0 parameters.gamma ell grade inputDimension outputDimension
    ⟨weightedSingle L parameters.sigma0 parameters.gamma ell grade cell
      (scaledOriginalJet ell mapping (field.1 cell)),
      Submodule.subset_span (Set.mem_range.mpr
        ⟨(cell, scaledOriginalJet ell mapping (field.1 cell)), rfl⟩)⟩

theorem originalCoefficientCell_norm_le {dimension inputDimension outputDimension : ℕ}
    (parameters : PhaseParameters) (L ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (cell : ℤ) :
    ‖originalCoefficientCell parameters L ell grade mapping field cell‖ ≤
      ∑ index : DerivativeIndex grade,
        ‖weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade cell
          (scaledOriginalJet ell mapping (field.1 cell)) index‖ := by
  change ‖weightedSingle L parameters.sigma0 parameters.gamma ell grade cell
    (scaledOriginalJet ell mapping (field.1 cell))‖ ≤ _
  unfold weightedSingle
  exact (norm_sum_le _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro index _membership
    exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1) _ _)

theorem originalCoefficientCell_norm_summable
    {dimension inputDimension outputDimension : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (grade : ℕ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) :
    Summable (fun cell : ℤ => ‖originalCoefficientCell parameters L ell grade mapping field cell‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (originalCoefficientCell_norm_le parameters L ell grade mapping field)
  exact (hasSum_sum fun index _ =>
    (scaledOriginalJet_weightedDerivative_summable parameters admissible mapping field index).hasSum).summable

theorem originalCoefficientCell_summable
    {dimension inputDimension outputDimension : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (grade : ℕ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) :
    Summable (originalCoefficientCell parameters L ell grade mapping field) :=
  (originalCoefficientCell_norm_summable parameters admissible grade mapping field).of_norm

/-- The actual completed AP8 coefficient, as the convergent sum of its literal
finite-cell rescaled original closed jets. -/
def originalCoefficient {dimension inputDimension outputDimension : ℕ}
    (parameters : PhaseParameters) (L ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) :
    Coefficient L parameters.sigma0 parameters.gamma ell grade inputDimension outputDimension :=
  ∑' cell : ℤ, originalCoefficientCell parameters L ell grade mapping field cell

def originalCoefficientConstant (parameters : PhaseParameters) (grade : ℕ) : ℝ :=
  ∑ index : DerivativeIndex grade, originalDerivativeSumConstant parameters (derivativeOrder index)

theorem originalCoefficientConstant_nonnegative (parameters : PhaseParameters) (grade : ℕ) :
    0 ≤ originalCoefficientConstant parameters grade :=
  Finset.sum_nonneg fun _index _ => originalDerivativeSumConstant_nonnegative parameters _

/-- AP18: exact three-grade loss, the original width, and the supremum over
each individual closed derivative before summation over the integer cells. -/
theorem originalCoefficient_norm_bound
    {dimension inputDimension outputDimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : GradeCore parameters dimension (grade + 3)) :
    ‖originalCoefficient parameters L ell grade mapping field.toCore‖ ≤
      originalCoefficientConstant parameters grade * ‖mapping‖ * ‖field‖ := by
  unfold originalCoefficient
  calc
    _ ≤ ∑' cell : ℤ, ‖originalCoefficientCell parameters L ell grade mapping field.toCore cell‖ :=
      norm_tsum_le_tsum_norm (originalCoefficientCell_norm_summable parameters admissible
        grade mapping field.toCore)
    _ ≤ ∑' cell : ℤ, ∑ index : DerivativeIndex grade,
        ‖weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade cell
          (scaledOriginalJet ell mapping (field.toCore.1 cell)) index‖ :=
      (originalCoefficientCell_norm_summable parameters admissible grade mapping field.toCore).tsum_le_tsum
        (originalCoefficientCell_norm_le parameters L ell grade mapping field.toCore)
        (hasSum_sum fun index _ => (scaledOriginalJet_weightedDerivative_summable parameters
          admissible mapping field.toCore index).hasSum).summable
    _ = ∑ index : DerivativeIndex grade, ∑' cell : ℤ,
        ‖weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade cell
          (scaledOriginalJet ell mapping (field.toCore.1 cell)) index‖ := by
      exact Summable.tsum_finsetSum fun index _ =>
        scaledOriginalJet_weightedDerivative_summable parameters admissible mapping field.toCore index
    _ ≤ ∑ index : DerivativeIndex grade,
        ‖mapping‖ * (originalDerivativeSumConstant parameters (derivativeOrder index) * ‖field‖) := by
      exact Finset.sum_le_sum fun index _ =>
        scaledOriginalJet_weightedDerivative_tsum_bound parameters admissible mapping field index
    _ = _ := by
      unfold originalCoefficientConstant
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro index _membership
      ring

theorem originalCoefficient_weightedDerivative
    {dimension inputDimension outputDimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (cell : ℤ) (index : DerivativeIndex grade) :
    weightedDerivative (originalCoefficient parameters L ell grade mapping field) cell index =
      weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade cell
        (scaledOriginalJet ell mapping (field.1 cell)) index := by
  let evaluate : Coefficient L parameters.sigma0 parameters.gamma ell grade
      inputDimension outputDimension →L[ℂ]
      C(ClosedDisk, OperatorValue inputDimension outputDimension) :=
    (lp.evalCLM ℂ (fun _ : ℤ × DerivativeIndex grade =>
      C(ClosedDisk, OperatorValue inputDimension outputDimension)) 1 (cell, index)).comp
      (smoothCore L parameters.sigma0 parameters.gamma ell grade
        inputDimension outputDimension).topologicalClosure.subtypeL
  change evaluate (∑' other : ℤ, originalCoefficientCell parameters L ell grade mapping field other) = _
  rw [evaluate.map_tsum (originalCoefficientCell_summable parameters admissible grade mapping field)]
  have each (other : ℤ) : evaluate (originalCoefficientCell parameters L ell grade mapping field other) =
      if cell = other then weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade other
        (scaledOriginalJet ell mapping (field.1 other)) index else 0 := by
    exact weightedSingle_apply L parameters.sigma0 parameters.gamma ell grade other cell
      (scaledOriginalJet ell mapping (field.1 other)) index
  simp_rw [each]
  simp

theorem originalCoefficient_derivative
    {dimension inputDimension outputDimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (originalCoefficient parameters L ell grade mapping field) cell index point =
      (ell ^ derivativeOrder index : ℂ) • mapping
        (closedMultiDerivative (field.1 cell) (derivativeMultiIndex index) (radialPoint ell point)) := by
  change ((coefficientScale L parameters.sigma0 parameters.gamma ell grade cell index point : ℂ)⁻¹) •
    weightedDerivative (originalCoefficient parameters L ell grade mapping field) cell index point = _
  rw [originalCoefficient_weightedDerivative parameters admissible]
  change ((coefficientScale L parameters.sigma0 parameters.gamma ell grade cell index point : ℂ)⁻¹) •
    ((coefficientScale L parameters.sigma0 parameters.gamma ell grade cell index point : ℂ) •
      smoothOperatorDerivative (scaledOriginalJet ell mapping (field.1 cell))
        (derivativeMultiIndex index) point) = _
  rw [← mul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (coefficientScale_pos L parameters.sigma0 parameters.gamma ell grade cell index point).ne'), one_smul]
  exact scaledOriginalJet_derivative admissible.2.2.2.1.le
    (admissible.2.2.2.2.trans (min_le_left _ _)) mapping (field.1 cell) (derivativeMultiIndex index) point

end Grad.GaugeCoefficients.Physical
