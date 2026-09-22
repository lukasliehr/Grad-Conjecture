import GQC61LiteralGaugeBlocks

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- The original full-cell, all-Cartesian-derivative C_ell^q norm of one
literal block, with the original envelope and remaining cell moment. -/
def gaugeBlockNorm {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3)
    (outer : OperatorValue 3 output) (inner : OperatorValue input 3) : ℝ :=
  ∑ index : DerivativeIndex grade, ∑' cell : ℤ,
    ‖operatorBlockMap outer inner (weightedDerivative coefficient cell index)‖

def gaugeEpsilon {L sigma gamma ell : ℝ} {grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3) : ℝ :=
  gaugeBlockNorm coefficient planarPartMap planarInclusionMap +
    gaugeBlockNorm coefficient planarPartMap toroidalInclusionMap +
    (gaugeBlockNorm coefficient toroidalPartMap planarInclusionMap +
     gaugeBlockNorm coefficient toroidalPartMap toroidalInclusionMap)

theorem gaugeBlockNorm_nonnegative {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3)
    (outer : OperatorValue 3 output) (inner : OperatorValue input 3) : 0 ≤ gaugeBlockNorm coefficient outer inner := by
  unfold gaugeBlockNorm
  positivity

theorem gaugeEpsilon_nonnegative {L sigma gamma ell : ℝ} {grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3) : 0 ≤ gaugeEpsilon coefficient :=
  add_nonneg (add_nonneg (gaugeBlockNorm_nonnegative coefficient _ _) (gaugeBlockNorm_nonnegative coefficient _ _))
    (add_nonneg (gaugeBlockNorm_nonnegative coefficient _ _) (gaugeBlockNorm_nonnegative coefficient _ _))

theorem gaugeBlockNorm_summable {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3)
    (outer : OperatorValue 3 output) (inner : OperatorValue input 3)
    (outerSmall : ‖outer‖ ≤ 1) (innerSmall : ‖inner‖ ≤ 1) (index : DerivativeIndex grade) :
    Summable (fun cell : ℤ => ‖operatorBlockMap outer inner (weightedDerivative coefficient cell index)‖) :=
  Summable.of_nonneg_of_le (fun cell => norm_nonneg (operatorBlockMap outer inner (weightedDerivative coefficient cell index)))
    (fun _ => operatorBlockMap_norm_le outer inner _ outerSmall innerSmall)
    (coordinate_norm_summable coefficient.val index)

theorem coefficient_norm_le_gaugeEpsilon {L sigma gamma ell : ℝ} {grade : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3) : ‖coefficient‖ ≤ gaugeEpsilon coefficient := by
  have coordinateBound (index : DerivativeIndex grade) :
      (∑' cell : ℤ, ‖weightedDerivative coefficient cell index‖) ≤
        (∑' cell : ℤ, ‖operatorBlockMap planarPartMap planarInclusionMap (weightedDerivative coefficient cell index)‖) +
        (∑' cell : ℤ, ‖operatorBlockMap planarPartMap toroidalInclusionMap (weightedDerivative coefficient cell index)‖) +
        ((∑' cell : ℤ, ‖operatorBlockMap toroidalPartMap planarInclusionMap (weightedDerivative coefficient cell index)‖) +
         (∑' cell : ℤ, ‖operatorBlockMap toroidalPartMap toroidalInclusionMap (weightedDerivative coefficient cell index)‖)) := by
    have pp := gaugeBlockNorm_summable coefficient planarPartMap planarInclusionMap planarPartMap_norm_le planarInclusionMap_norm_le index
    have pt := gaugeBlockNorm_summable coefficient planarPartMap toroidalInclusionMap planarPartMap_norm_le toroidalInclusionMap_norm_le index
    have tp := gaugeBlockNorm_summable coefficient toroidalPartMap planarInclusionMap toroidalPartMap_norm_le planarInclusionMap_norm_le index
    have tt := gaugeBlockNorm_summable coefficient toroidalPartMap toroidalInclusionMap toroidalPartMap_norm_le toroidalInclusionMap_norm_le index
    exact ((coordinate_norm_summable coefficient.val index).tsum_le_tsum
      (fun cell => operatorMap_norm_four_blocks (weightedDerivative coefficient cell index)) ((pp.add pt).add (tp.add tt))).trans_eq
        ((pp.add pt).tsum_add (tp.add tt) |>.trans (congrArg₂ (fun first second : ℝ => first + second) (pp.tsum_add pt) (tp.tsum_add tt)))
  calc
    ‖coefficient‖ = ∑ index : DerivativeIndex grade, ∑' cell : ℤ, ‖weightedDerivative coefficient cell index‖ := by
      rw [coefficient_norm_formula]
      exact Summable.tsum_finsetSum (fun index _ => coordinate_norm_summable coefficient.val index)
    _ ≤ _ := Finset.sum_le_sum (fun index _ => coordinateBound index)
    _ = gaugeEpsilon coefficient := by simp only [gaugeEpsilon, gaugeBlockNorm, Finset.sum_add_distrib]

theorem operatorBlockMap_weighted_literal {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade 3 3)
    (outer : OperatorValue 3 output) (inner : OperatorValue input 3)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    operatorBlockMap outer inner (weightedDerivative coefficient cell index) point =
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        ((outer.comp (coefficientDerivative coefficient cell index point)).comp inner) := by
  change (outer.comp (weightedDerivative coefficient cell index point)).comp inner = _
  rw [weighted_derivative_literal]
  apply ContinuousLinearMap.ext
  intro value
  change outer ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
    coefficientDerivative coefficient cell index point (inner value)) = _
  exact map_smul outer _ _

end Grad.GaugeCoefficients.Physical.Compensated
