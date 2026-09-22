import AKBU3ActualHighIncomingPhysicalCoefficient
import AKBU4OriginalIncomingFrequencyWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularRestriction Grad.AnnularSourceGraph
open Grad.AnnularLowEnergy Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularVariational Grad.GaugeCoefficients.Physical.WeightedTrace Grad.PhaseAlgebra
open Grad.SourceCollarCoefficients Grad.OriginalKernelRetainedDecay Grad.AnnularFluxTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower) (bounded : lower<1)
    (lengthPositive : 0<length) (field : CoupledSpace lower length positive lengthPositive)
    (xi rotatedXi : CellL2 1)
    (represented : ∀ mode,sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0
      ⟨lower,le_rfl,bounded.le⟩ mode=lambdaCircleCoefficient parameters lower xi mode)

include represented

theorem originalHighIncoming_weighted (mode : HighAnnularMode) :
    annularEnergyTrace lower length positive bounded lengthPositive 0 (bEnergyDecode lower length positive field.ofLp.1.ofLp.1) mode=
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)/cellFrequency mode.val.2*lower^(-(9/4:ℝ))) • xi mode.val := by
  rw [originalHighIncoming_physical parameters lower length positive bounded lengthPositive field mode,represented]
  rw [lambdaCircleCoefficient,←Complex.ofReal_inv,Complex.coe_smul,smul_smul]
  congr 1
  unfold lambdaCircleWeight
  field_simp [(Real.exp_pos _).ne',(cellFrequency_pos mode.val.2).ne']

/-- SAME actual high incoming norm, controlled by original lambda-weighted
Xi and its genuine rotation. The singular factor is exactly r^-9/4. -/
theorem originalHighIncoming_norm_bound
    (rotation : OriginalCircleRotation xi rotatedXi) :
    ‖annularEnergyTrace lower length positive bounded lengthPositive 0 (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)‖≤
      (2*lower^(-(9/4:ℝ)))*(‖xi‖+‖rotatedXi‖) := by
  let trace := annularEnergyTrace lower length positive bounded lengthPositive 0 (bEnergyDecode lower length positive field.ofLp.1.ofLp.1)
  have factor : 0≤2*lower^(-(9/4:ℝ)) := by positivity
  have coefficient (mode : ℤ×ℤ) : ‖highHilbertIntoFull trace mode‖≤
      (2*lower^(-(9/4:ℝ)))*(‖xi mode‖+‖rotatedXi mode‖) := by
    by_cases high : 3≤|mode.1|
    · change ‖(if large : 3≤|mode.1| then trace ⟨mode,large⟩ else 0)‖≤_
      rw [dif_pos high]
      have actual := originalHighIncoming_weighted parameters lower length positive bounded lengthPositive field xi represented ⟨mode,high⟩
      change trace ⟨mode,high⟩=_ at actual
      have frequencyPositive := Grad.AnnularFluxTrace.annularFrequency_pos (⟨mode,high⟩ : HighAnnularMode)
      have cellPositive := cellFrequency_pos mode.2
      rw [actual,norm_smul,Real.norm_of_nonneg (by positivity)]
      have rotated : ‖rotatedXi mode‖= |(mode.1:ℝ)| *‖xi mode‖ := by
        rw [rotation mode,norm_smul,norm_mul,Complex.norm_I,one_mul,Complex.norm_intCast]
      rw [rotated]
      have paid := mul_le_mul_of_nonneg_right (originalHighFrequency_payment mode)
        (mul_nonneg (Real.rpow_nonneg positive.le (-(9/4:ℝ))) (norm_nonneg (xi mode)))
      nlinarith only [paid]
    · change ‖(if large : 3≤|mode.1| then trace ⟨mode,large⟩ else 0)‖≤_
      rw [dif_neg high,norm_zero]
      positivity
  calc
    _ = ‖highHilbertIntoFull trace‖ := (highHilbertIntoFull.norm_map trace).symm
    _ ≤ ‖(2*lower^(-(9/4:ℝ))) • (lpNormFamily xi+lpNormFamily rotatedXi)‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      change ‖highHilbertIntoFull trace mode‖≤‖(2*lower^(-(9/4:ℝ)))*(‖xi mode‖+‖rotatedXi mode‖)‖
      rw [Real.norm_of_nonneg (mul_nonneg factor (add_nonneg (norm_nonneg _) (norm_nonneg _)))]
      exact coefficient mode
    _ = (2*lower^(-(9/4:ℝ)))*‖lpNormFamily xi+lpNormFamily rotatedXi‖ := by rw [norm_smul,Real.norm_of_nonneg factor]
    _ ≤ (2*lower^(-(9/4:ℝ)))*(‖lpNormFamily xi‖+‖lpNormFamily rotatedXi‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) factor
    _ = _ := by rw [lpNormFamily_norm,lpNormFamily_norm]

end Grad.OriginalPhysicalKernelUniqueness
