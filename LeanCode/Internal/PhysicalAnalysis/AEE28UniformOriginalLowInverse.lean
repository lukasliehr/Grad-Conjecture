import AEE27CompleteLowReferenceSurjectivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowReferenceLinearEquiv (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    lowEnergyGraph lower length positive ≃ₗ[ℂ] LowEnergyData lower :=
  LinearEquiv.ofBijective (lowReferenceDataOperator parameters length lower lengthPositive positive bounded).toLinearMap
    (lowReferenceDataOperator_bijective parameters length lower lengthPositive positive bounded)

theorem lowReferenceLinearEquiv_apply (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    lowReferenceLinearEquiv parameters length lower lengthPositive positive bounded field =
      lowReferenceDataOperator parameters length lower lengthPositive positive bounded field := rfl

theorem lowReferenceLinearEquiv_inverse_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) (data : LowEnergyData lower) :
    ‖(lowReferenceLinearEquiv parameters length lower lengthPositive positive bounded).symm data‖ ≤
      Real.sqrt (lowReferenceGraphConstant parameters length) * ‖data‖ := by
  have bound := lowReferenceDataOperator_lowerBound parameters length lower lengthPositive positive bounded
    ((lowReferenceLinearEquiv parameters length lower lengthPositive positive bounded).symm data)
  rw [← lowReferenceLinearEquiv_apply, LinearEquiv.apply_symm_apply] at bound
  exact bound

/-- Actual reference inverse on the complete original low graph. Its operator
bound is independent of the inner radius. -/
def lowReferenceInverse (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    LowEnergyData lower →L[ℂ] lowEnergyGraph lower length positive :=
  (lowReferenceLinearEquiv parameters length lower lengthPositive positive bounded).symm.toLinearMap.mkContinuous
    (Real.sqrt (lowReferenceGraphConstant parameters length))
    (lowReferenceLinearEquiv_inverse_bound parameters length lower lengthPositive positive bounded)

theorem lowReferenceInverse_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) (data : LowEnergyData lower) :
    ‖lowReferenceInverse parameters length lower lengthPositive positive bounded data‖ ≤
      Real.sqrt (lowReferenceGraphConstant parameters length) * ‖data‖ :=
  lowReferenceLinearEquiv_inverse_bound parameters length lower lengthPositive positive bounded data

theorem lowReferenceDataOperator_inverse (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) (data : LowEnergyData lower) :
    lowReferenceDataOperator parameters length lower lengthPositive positive bounded
      (lowReferenceInverse parameters length lower lengthPositive positive bounded data) = data :=
  (lowReferenceLinearEquiv parameters length lower lengthPositive positive bounded).apply_symm_apply data

theorem lowReferenceInverse_dataOperator (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    lowReferenceInverse parameters length lower lengthPositive positive bounded
      (lowReferenceDataOperator parameters length lower lengthPositive positive bounded field) = field :=
  (lowReferenceLinearEquiv parameters length lower lengthPositive positive bounded).symm_apply_apply field

def lowReferenceContinuousEquiv (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    lowEnergyGraph lower length positive ≃L[ℂ] LowEnergyData lower where
  toLinearEquiv := lowReferenceLinearEquiv parameters length lower lengthPositive positive bounded
  continuous_toFun := (lowReferenceDataOperator parameters length lower lengthPositive positive bounded).continuous
  continuous_invFun := (lowReferenceInverse parameters length lower lengthPositive positive bounded).continuous

end Grad.AnnularLowCompletion
