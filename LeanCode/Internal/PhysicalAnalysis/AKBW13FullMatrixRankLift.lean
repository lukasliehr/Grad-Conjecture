import AKBW12UniformFixedRankKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation

namespace StartupRankOperator

private def entrywiseCoarse {input output : ℕ} (rank : ℕ) (operator : StartupL2 input →L[ℂ] StartupL2 output) :
    StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank) :=
  (startupTensorFieldEquiv output rank).toLinearIsometry.toContinuousLinearMap.comp
    ((hilbertLift (Index := DerivativeIndex rank) operator).comp
      (startupTensorFieldEquiv input rank).symm.toLinearIsometry.toContinuousLinearMap)

private def entrywiseFine {input output : ℕ} (rank : ℕ) (operator : StartupFirst input →L[ℂ] StartupFirst output) :
    StartupFirst (startupTensorDimension input rank) →L[ℂ] StartupFirst (startupTensorDimension output rank) :=
  (startupTensorFirstEquiv output rank).toLinearIsometry.toContinuousLinearMap.comp
    ((hilbertLift (Index := DerivativeIndex rank) operator).comp
      (startupTensorFirstEquiv input rank).symm.toLinearIsometry.toContinuousLinearMap)

def entrywise {input output : ℕ} (rank : ℕ) (coarse : StartupL2 input →L[ℂ] StartupL2 output)
    (fine : StartupFirst input →L[ℂ] StartupFirst output) (same : StartupCompatible coarse fine) :
    StartupRankOperator rank input output := by
  refine { coarse := entrywiseCoarse rank coarse
           fine := entrywiseFine rank fine
           compatible := ?_
           bound := ‖coarse‖ + ‖fine‖
           nonnegative := add_nonneg (norm_nonneg coarse) (norm_nonneg fine)
           coarse_bound := ?_
           fine_bound := ?_ }
  · intro field
    change startupFirstValue (startupTensorFirstEquiv output rank
      (hilbertLift (Index := DerivativeIndex rank) fine ((startupTensorFirstEquiv input rank).symm field))) =
      startupTensorFieldEquiv output rank (hilbertLift (Index := DerivativeIndex rank) coarse
        ((startupTensorFieldEquiv input rank).symm (startupFirstValue field)))
    rw [startupTensorFirstEquiv_base]
    apply congrArg (startupTensorFieldEquiv output rank)
    rw [← startupTensorFirstEquiv_symm_values input rank field]
    apply PiLp.ext
    intro word
    exact same ((startupTensorFirstEquiv input rank).symm field word)
  · apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg coarse) (norm_nonneg fine))
    intro field
    change ‖startupTensorFieldEquiv output rank
      (hilbertLift (Index := DerivativeIndex rank) coarse ((startupTensorFieldEquiv input rank).symm field))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (hilbertLiftLinear_norm_le coarse _).trans (by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg fine)) (norm_nonneg field))
  · apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg coarse) (norm_nonneg fine))
    intro field
    change ‖startupTensorFirstEquiv output rank
      (hilbertLift (Index := DerivativeIndex rank) fine ((startupTensorFirstEquiv input rank).symm field))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (hilbertLiftLinear_norm_le fine _).trans (by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg coarse)) (norm_nonneg field))

theorem entrywise_coarse {input output : ℕ} (rank : ℕ) (coarse : StartupL2 input →L[ℂ] StartupL2 output)
    (fine : StartupFirst input →L[ℂ] StartupFirst output) (same : StartupCompatible coarse fine)
    (fields : Tensor rank (StartupL2 input)) :
    (entrywise rank coarse fine same).coarse (startupTensorFieldEquiv input rank fields) =
      startupTensorFieldEquiv output rank (hilbertLift (Index := DerivativeIndex rank) coarse fields) := by
  change startupTensorFieldEquiv output rank
    (hilbertLift (Index := DerivativeIndex rank) coarse
      ((startupTensorFieldEquiv input rank).symm (startupTensorFieldEquiv input rank fields))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

def matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (rank : ℕ) (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) : StartupRankOperator rank input output :=
  entrywise rank (originalMatrixKernel admissible family coherent)
    (startupMatrixFirstGraphCLM admissible family coherent) (startupMatrixFirstGraph_compatible admissible family coherent)

theorem matrix_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (rank : ℕ) (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) :
    (matrix admissible rank family coherent).bound =
      ‖originalMatrixKernel admissible family coherent‖ + ‖startupMatrixFirstGraphCLM admissible family coherent‖ := rfl

end StartupRankOperator
end Grad.CartesianStartup
