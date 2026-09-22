import GC14FrameInterface

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set
open scoped BigOperators ENNReal Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

local instance {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ} :
    CompleteSpace (Coefficient L sigma gamma ell grade inputDimension outputDimension) := by
  unfold Coefficient
  infer_instance

def familyCell (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension) (cell : ℤ) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  coreInclusion L sigma gamma ell grade inputDimension outputDimension
    ⟨weightedSingle L sigma gamma ell grade cell (fields cell),
      Submodule.subset_span (Set.mem_range.mpr ⟨(cell, fields cell), rfl⟩)⟩

def familySummable (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension) : Prop :=
  ∀ index : DerivativeIndex grade,
    Summable (fun cell : ℤ => ‖weightedSmoothDerivative L sigma gamma ell grade cell (fields cell) index‖)

theorem familyCell_norm_le (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension) (cell : ℤ) :
    ‖familyCell L sigma gamma ell grade fields cell‖ ≤
      ∑ index : DerivativeIndex grade,
        ‖weightedSmoothDerivative L sigma gamma ell grade cell (fields cell) index‖ := by
  change ‖weightedSingle L sigma gamma ell grade cell (fields cell)‖ ≤ _
  unfold weightedSingle
  exact (norm_sum_le _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro index _membership
    exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1) _ _)

theorem familyCell_norm_summable {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension)
    (summability : familySummable L sigma gamma ell grade fields) :
    Summable (fun cell : ℤ => ‖familyCell L sigma gamma ell grade fields cell‖) := by
  exact Summable.of_nonneg_of_le
    (fun cell => norm_nonneg (familyCell L sigma gamma ell grade fields cell))
    (familyCell_norm_le L sigma gamma ell grade fields)
    (hasSum_sum fun index _ => (summability index).hasSum).summable

/-- Internal completion constructor. Each actual state or seed family below
supplies its own proved summability; it is never a public frame hypothesis. -/
def familyCoefficient (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension) :
    Coefficient L sigma gamma ell grade inputDimension outputDimension :=
  ∑' cell : ℤ, familyCell L sigma gamma ell grade fields cell

theorem familyCoefficient_weightedDerivative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension)
    (summability : familySummable L sigma gamma ell grade fields)
    (cell : ℤ) (index : DerivativeIndex grade) :
    weightedDerivative (familyCoefficient L sigma gamma ell grade fields) cell index =
      weightedSmoothDerivative L sigma gamma ell grade cell (fields cell) index := by
  let evaluate : Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      C(ClosedDisk, OperatorValue inputDimension outputDimension) :=
    (lp.evalCLM ℂ (fun _ : ℤ × DerivativeIndex grade =>
      C(ClosedDisk, OperatorValue inputDimension outputDimension)) 1 (cell, index)).comp
      (smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure.subtypeL
  change evaluate (∑' other : ℤ, familyCell L sigma gamma ell grade fields other) = _
  rw [evaluate.map_tsum (familyCell_norm_summable fields summability).of_norm]
  have each (other : ℤ) : evaluate (familyCell L sigma gamma ell grade fields other) =
      if cell = other then weightedSmoothDerivative L sigma gamma ell grade other (fields other) index
        else 0 := weightedSingle_apply L sigma gamma ell grade other cell (fields other) index
  simp_rw [each]
  simp

theorem familyCoefficient_derivative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension)
    (summability : familySummable L sigma gamma ell grade fields)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (familyCoefficient L sigma gamma ell grade fields) cell index point =
      smoothOperatorDerivative (fields cell) (derivativeMultiIndex index) point := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    weightedDerivative (familyCoefficient L sigma gamma ell grade fields) cell index point = _
  rw [familyCoefficient_weightedDerivative fields summability]
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ) •
      smoothOperatorDerivative (fields cell) (derivativeMultiIndex index) point) = _
  rw [← mul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (coefficientScale_pos L sigma gamma ell grade cell index point).ne'), one_smul]

theorem familyCoefficient_norm_formula {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (fields : ℤ → SmoothOperatorJet inputDimension outputDimension)
    (summability : familySummable L sigma gamma ell grade fields) :
    ‖familyCoefficient L sigma gamma ell grade fields‖ =
      ∑ index : DerivativeIndex grade, ∑' cell : ℤ,
        ‖weightedSmoothDerivative L sigma gamma ell grade cell (fields cell) index‖ := by
  rw [coefficient_norm_formula]
  simp_rw [familyCoefficient_weightedDerivative fields summability]
  exact Summable.tsum_finsetSum fun index _ => summability index

end Grad.GaugeCoefficients.Physical.Frame
