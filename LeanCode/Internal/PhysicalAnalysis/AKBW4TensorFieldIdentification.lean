import AKBW3FiniteTensorValueIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap

private theorem lpValueInverse {Input Output Point : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    [MeasurableSpace Point] (measure : Measure Point)
    (equivalence : Input ≃ₗᵢ[ℂ] Output) (field : Lp Input 2 measure) :
    equivalence.symm.toLinearIsometry.toContinuousLinearMap.compLpL 2 measure
      (equivalence.toLinearIsometry.toContinuousLinearMap.compLpL 2 measure field) = field := by
  apply Lp.ext
  filter_upwards [equivalence.toLinearIsometry.toContinuousLinearMap.coeFn_compLpL field,
    equivalence.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (equivalence.toLinearIsometry.toContinuousLinearMap.compLpL 2 measure field)] with point forward backward
  rw [backward,forward]
  exact equivalence.symm_apply_apply (field point)

/-- Value isometries lift to the same L2 representative, without changing the
spatial measure or completing a different field. -/
def startupLpValueEquiv {Input Output Point : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    [MeasurableSpace Point] (measure : Measure Point)
    (equivalence : Input ≃ₗᵢ[ℂ] Output) : Lp Input 2 measure ≃ₗᵢ[ℂ] Lp Output 2 measure where
  toFun := equivalence.toLinearIsometry.toContinuousLinearMap.compLpL 2 measure
  invFun := equivalence.symm.toLinearIsometry.toContinuousLinearMap.compLpL 2 measure
  left_inv := lpValueInverse measure equivalence
  right_inv field := by
    have same := lpValueInverse measure equivalence.symm field
    simpa only [LinearIsometryEquiv.symm_symm] using same
  map_add' := map_add _
  map_smul' := map_smul _
  norm_map' field := by
    rw [Lp.norm_def,Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [equivalence.toLinearIsometry.toContinuousLinearMap.coeFn_compLpL field] with point same
    change ‖equivalence.toLinearIsometry.toContinuousLinearMap.compLpL 2 measure field point‖ = ‖field point‖
    rw [same]
    exact equivalence.norm_map (field point)

def startupTensorFieldEquiv (dimension rank : ℕ) :
    Tensor rank (StartupL2 dimension) ≃ₗᵢ[ℂ] StartupL2 (startupTensorDimension dimension rank) :=
  (Grad.TensorLpExchange.Generic.exchange (DerivativeIndex rank) (Grad.GenericCarriers.CellValues dimension)
    (volume.restrict openUnitDisk)).trans
      (startupLpValueEquiv (volume.restrict openUnitDisk) (startupTensorCellEquiv dimension rank))

theorem startupTensorFieldEquiv_ae (dimension rank : ℕ)
    (fields : Tensor rank (StartupL2 dimension)) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupTensorFieldEquiv dimension rank fields point cell =
        startupTensorValueEquiv dimension rank (WithLp.toLp 2 (fun word => fields word point cell)) := by
  filter_upwards [Grad.TensorLpExchange.Generic.collect_ae (DerivativeIndex rank)
    (Grad.GenericCarriers.CellValues dimension) (volume.restrict openUnitDisk) fields,
    (startupTensorCellEquiv dimension rank).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (Grad.TensorLpExchange.Generic.exchange (DerivativeIndex rank) (Grad.GenericCarriers.CellValues dimension)
        (volume.restrict openUnitDisk) fields)] with point collected transformed
  intro cell
  apply (congrArg (fun value : Grad.GenericCarriers.CellValues (startupTensorDimension dimension rank) => value cell) transformed).trans
  change startupTensorValueEquiv dimension rank (WithLp.toLp 2 (fun word =>
    Grad.TensorLpExchange.Generic.exchange (DerivativeIndex rank) (Grad.GenericCarriers.CellValues dimension)
      (volume.restrict openUnitDisk) fields point word cell)) = _
  apply congrArg (startupTensorValueEquiv dimension rank)
  apply PiLp.ext
  intro word
  exact congrArg (fun value : Tensor rank (Grad.GenericCarriers.CellValues dimension) => value word cell) collected

end Grad.CartesianStartup
