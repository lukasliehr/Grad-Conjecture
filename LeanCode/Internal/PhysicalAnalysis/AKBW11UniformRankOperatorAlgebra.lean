import AKBW10FixedTensorGraphBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap

/-- The same genuine operator on the L2 and first-graph tensor identifications.
The numerical bound is tracked through the actual finite formula. -/
structure StartupRankOperator (rank input output : ℕ) where
  coarse : StartupL2 (startupTensorDimension input rank) →L[ℂ] StartupL2 (startupTensorDimension output rank)
  fine : StartupFirst (startupTensorDimension input rank) →L[ℂ] StartupFirst (startupTensorDimension output rank)
  compatible : StartupCompatible coarse fine
  bound : ℝ
  nonnegative : 0 ≤ bound
  coarse_bound : ‖coarse‖ ≤ bound
  fine_bound : ‖fine‖ ≤ bound

private theorem startupRankScalar_norm {Input Output : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    (scalar : ℂ) (operator : Input →L[ℂ] Output) :
    ‖scalar • operator‖ ≤ ‖scalar‖ * ‖operator‖ := (norm_smul scalar operator).le

namespace StartupRankOperator

variable {rank input middle output : ℕ}

def identity (rank dimension : ℕ) : StartupRankOperator rank dimension dimension where
  coarse := ContinuousLinearMap.id ℂ _
  fine := ContinuousLinearMap.id ℂ _
  compatible := startupCompatible_id _
  bound := 1
  nonnegative := zero_le_one
  coarse_bound := ContinuousLinearMap.norm_id_le
  fine_bound := ContinuousLinearMap.norm_id_le

def add (first second : StartupRankOperator rank input output) : StartupRankOperator rank input output where
  coarse := first.coarse + second.coarse
  fine := first.fine + second.fine
  compatible := startupCompatible_add first.compatible second.compatible
  bound := first.bound + second.bound
  nonnegative := add_nonneg first.nonnegative second.nonnegative
  coarse_bound := (norm_add_le first.coarse second.coarse).trans (add_le_add first.coarse_bound second.coarse_bound)
  fine_bound := (norm_add_le first.fine second.fine).trans (add_le_add first.fine_bound second.fine_bound)

def sub (first second : StartupRankOperator rank input output) : StartupRankOperator rank input output where
  coarse := first.coarse - second.coarse
  fine := first.fine - second.fine
  compatible := startupCompatible_sub first.compatible second.compatible
  bound := first.bound + second.bound
  nonnegative := add_nonneg first.nonnegative second.nonnegative
  coarse_bound := (norm_sub_le first.coarse second.coarse).trans (add_le_add first.coarse_bound second.coarse_bound)
  fine_bound := (norm_sub_le first.fine second.fine).trans (add_le_add first.fine_bound second.fine_bound)

def smul (scalar : ℂ) (operator : StartupRankOperator rank input output) : StartupRankOperator rank input output where
  coarse := scalar • operator.coarse
  fine := scalar • operator.fine
  compatible := startupCompatible_smul scalar operator.compatible
  bound := ‖scalar‖ * operator.bound
  nonnegative := mul_nonneg (norm_nonneg _) operator.nonnegative
  coarse_bound := (startupRankScalar_norm scalar operator.coarse).trans
    (mul_le_mul_of_nonneg_left operator.coarse_bound (norm_nonneg _))
  fine_bound := (startupRankScalar_norm scalar operator.fine).trans
    (mul_le_mul_of_nonneg_left operator.fine_bound (norm_nonneg _))

def comp (outer : StartupRankOperator rank middle output) (inner : StartupRankOperator rank input middle) :
    StartupRankOperator rank input output where
  coarse := outer.coarse.comp inner.coarse
  fine := outer.fine.comp inner.fine
  compatible := startupCompatible_comp outer.compatible inner.compatible
  bound := outer.bound * inner.bound
  nonnegative := mul_nonneg outer.nonnegative inner.nonnegative
  coarse_bound := (ContinuousLinearMap.opNorm_comp_le outer.coarse inner.coarse).trans
    (mul_le_mul outer.coarse_bound inner.coarse_bound (norm_nonneg inner.coarse) outer.nonnegative)
  fine_bound := (ContinuousLinearMap.opNorm_comp_le outer.fine inner.fine).trans
    (mul_le_mul outer.fine_bound inner.fine_bound (norm_nonneg inner.fine) outer.nonnegative)

end StartupRankOperator
end Grad.CartesianStartup
