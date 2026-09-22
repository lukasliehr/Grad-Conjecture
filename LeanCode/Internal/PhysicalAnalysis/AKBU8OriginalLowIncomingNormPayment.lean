import AKBU6ActualLowIncomingWeightedCoefficients
import AKBU7OriginalLowIncomingWeightBounds
import AEM7LiteralLowBoundaryCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators ENNReal
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularLowEnergy Grad.AnnularCoupledInverse
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularFluxTrace Grad.PhaseAlgebra
open Grad.OriginalKernelRetainedDecay Grad.AnnularCurrentLow

theorem originalLowBoundary_norm_sum (field : LowEnergyBoundary) :
    ‖field‖≤‖lowBoundaryComponent 0 field‖+‖lowBoundaryComponent 1 field‖ := by
  have total := lp.norm_rpow_eq_tsum (p:=2) (by norm_num) field
  have first := lp.norm_rpow_eq_tsum (p:=2) (by norm_num) (lowBoundaryComponent 0 field)
  have second := lp.norm_rpow_eq_tsum (p:=2) (by norm_num) (lowBoundaryComponent 1 field)
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat] at total first second
  have summable : Summable (fun index : LowAnnularIndex => ‖field index‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using field.property.summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  rw [summable.tsum_prod,tsum_fintype,Fin.sum_univ_two] at total
  change ‖field‖^2=(∑' mode:LowAnnularMode,‖lowBoundaryComponent 0 field mode‖^2)+
    (∑' mode:LowAnnularMode,‖lowBoundaryComponent 1 field mode‖^2) at total
  rw [←first,←second] at total
  nlinarith [norm_nonneg field,norm_nonneg (lowBoundaryComponent 0 field),norm_nonneg (lowBoundaryComponent 1 field)]

theorem originalLowBoundary_row_bound (field : LowEnergyBoundary) (row : Fin 2)
    (source : CellL2 1) (constant : ℝ) (nonnegative : 0≤constant)
    (coefficient : ∀ mode:LowAnnularMode,‖field (row,mode)‖≤constant*‖source mode.val‖) :
    ‖lowBoundaryComponent row field‖≤constant*‖source‖ := by
  calc
    _ = ‖lowBoundaryIntoFull (lowBoundaryComponent row field)‖ := (lowBoundaryIntoFull.norm_map _).symm
    _ ≤ ‖constant • lpNormFamily source‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      rw [show ‖(constant • lpNormFamily source) mode‖=constant*‖source mode‖ by
        change ‖constant*‖source mode‖‖=_
        rw [Real.norm_of_nonneg (mul_nonneg nonnegative (norm_nonneg _))]]
      by_cases low : |mode.1|=1 ∨ |mode.1|=2
      · rw [lowBoundaryIntoFull_retained _ ⟨mode,low⟩]
        exact coefficient ⟨mode,low⟩
      · rw [lowBoundaryIntoFull_outside _ mode low,norm_zero]
        positivity
    _ = _ := by rw [norm_smul,Real.norm_of_nonneg nonnegative,lpNormFamily_norm]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower) (bounded : lower<1)
    (lengthPositive : 0<length) (field : CoupledSpace lower length positive lengthPositive)
    (xi x : CellL2 1)
    (representedXi : ∀ mode,sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0
      ⟨lower,le_rfl,bounded.le⟩ mode=lambdaCircleCoefficient parameters lower xi mode)
    (representedX : ∀ mode,sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
      ⟨lower,le_rfl,bounded.le⟩ mode=lambdaCircleCoefficient parameters lower x mode)

include representedXi representedX

theorem originalLowIncoming_norm_bound :
    ‖lowIncomingTrace lower length positive bounded field.ofLp.2‖≤
      (((lowBalanceConstant length parameters.gamma+2)*(1+length⁻¹))*lower^(-(9/4:ℝ)))*‖xi‖+
      lower^(-(5/4:ℝ))*‖x‖ := by
  apply (originalLowBoundary_norm_sum _).trans
  apply add_le_add
  · apply originalLowBoundary_row_bound _ 0 xi _ (by unfold lowBalanceConstant; positivity)
    intro mode
    rw [originalLowIncoming_Xi parameters lower length positive bounded lengthPositive field xi representedXi mode,
      norm_smul,Real.norm_of_nonneg (by
        have amp := (lowAmplitude_pos length parameters.gamma mode).le
        have k := (cellFrequency_pos mode.val.2).le
        positivity)]
    exact mul_le_mul_of_nonneg_right (originalLowXi_weight_bound length parameters.gamma lower lengthPositive positive bounded.le mode) (norm_nonneg _)
  · apply originalLowBoundary_row_bound _ 1 x _ (Real.rpow_nonneg positive.le _)
    intro mode
    rw [originalLowIncoming_X parameters lower length positive bounded lengthPositive field x representedX mode,
      norm_smul,Real.norm_of_nonneg (by have k := (cellFrequency_pos mode.val.2).le; positivity)]
    exact mul_le_mul_of_nonneg_right (originalLowX_weight_bound length lower positive mode.val.2) (norm_nonneg _)

end Grad.OriginalPhysicalKernelUniqueness
