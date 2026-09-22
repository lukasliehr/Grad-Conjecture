import GC18APConvolution

noncomputable section

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem operatorHasSum_apply {Index First Second : Type}
    [NormedAddCommGroup First] [NormedSpace ℂ First] [NormedAddCommGroup Second] [NormedSpace ℂ Second]
    (family : Index → First →L[ℂ] Second) (target : First →L[ℂ] Second) (summed : HasSum family target) (field : First) :
    HasSum (fun index => family index field) (target field) :=
  (ContinuousLinearMap.apply ℂ Second field).hasSum summed

theorem apAllocatedOperator_hasSum {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade)
    (coefficient : WeightedAmbient grade inputDimension outputDimension) (field : APAmbient inputDimension grade) :
    HasSum (fun shift : ℤ => apSingleOperator (inputDimension := inputDimension) (outputDimension := outputDimension)
      (grade := grade) admissible allocation shift (coefficient (shift, apCoefficientIndex allocation)) field)
      (apAllocatedOperator (inputDimension := inputDimension) (outputDimension := outputDimension)
        (grade := grade) admissible allocation coefficient field) := by
  let family : ℤ → APAmbient inputDimension grade →L[ℂ] APAmbient outputDimension grade :=
    fun shift => apSingleOperator admissible allocation shift (coefficient (shift, apCoefficientIndex allocation))
  have summed : HasSum family (apAllocatedOperator admissible allocation coefficient) :=
    (apSingleOperator_norm_summable admissible allocation coefficient).of_norm.hasSum
  exact operatorHasSum_apply family (apAllocatedOperator admissible allocation coefficient) summed field

end Grad.GaugeCoefficients.Physical.RadialLedger
