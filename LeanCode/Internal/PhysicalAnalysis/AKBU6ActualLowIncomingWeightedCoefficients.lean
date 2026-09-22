import AKBU3ActualHighIncomingPhysicalCoefficient
import AKBU4OriginalIncomingFrequencyWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularRestriction Grad.AnnularSourceGraph
open Grad.AnnularLowEnergy Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularVariational Grad.GaugeCoefficients.Physical.WeightedTrace Grad.PhaseAlgebra
open Grad.SourceCollarCoefficients Grad.OriginalKernelRetainedDecay

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower) (bounded : lower<1)
    (lengthPositive : 0<length) (field : CoupledSpace lower length positive lengthPositive)

/-- Exact xi part of the original BE incoming pair, including a_m sqrt(mu)
and the SAME all-cell lambda weight. -/
theorem originalLowIncoming_Xi (xi : CellL2 1)
    (represented : ∀ mode,sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0
      ⟨lower,le_rfl,bounded.le⟩ mode=lambdaCircleCoefficient parameters lower xi mode) (mode : LowAnnularMode) :
    lowIncomingTrace lower length positive bounded field.ofLp.2 (0,mode)=
      (lowAmplitude length parameters.gamma mode*lower^(-(7/4:ℝ))*Real.sqrt (lowMu length lower mode.val.2)/cellFrequency mode.val.2) • xi mode.val := by
  have high : ¬3≤|mode.val.1| := by rcases mode.property with one|two <;> omega
  have actual := represented mode.val
  simp only [sameCoupledXiCoefficient,dif_neg high,dif_pos mode.property,pow_zero,Complex.ofReal_one,one_smul] at actual
  rw [lowIncomingTrace_apply]
  change (lower^(-(7/4:ℝ))*(Real.sqrt (lowMu length lower mode.val.2))⁻¹) •
    lowEnergySection lower length positive bounded field.ofLp.2 (0,mode) ⟨lower,le_rfl,bounded.le⟩=_
  rw [←lowPhysicalSection_xi parameters lower length positive bounded field.ofLp.2 mode ⟨lower,le_rfl,bounded.le⟩,actual]
  rw [lambdaCircleCoefficient,←Complex.ofReal_inv,Complex.coe_smul,smul_smul,smul_smul,smul_smul]
  congr 1
  unfold lambdaCircleWeight
  field_simp [(Real.exp_pos _).ne',(cellFrequency_pos mode.val.2).ne',
    (Real.sqrt_pos.mpr (lowMu_pos length lower mode.val.2 positive)).ne']
  rw [Real.sq_sqrt (lowMu_nonneg _ _ _)]
  ring

/-- Exact x part of the SAME original BE incoming pair. -/
theorem originalLowIncoming_X (x : CellL2 1)
    (represented : ∀ mode,sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
      ⟨lower,le_rfl,bounded.le⟩ mode=lambdaCircleCoefficient parameters lower x mode) (mode : LowAnnularMode) :
    lowIncomingTrace lower length positive bounded field.ofLp.2 (1,mode)=
      (lower^(-(7/4:ℝ))*(Real.sqrt (lowMu length lower mode.val.2))⁻¹/cellFrequency mode.val.2) • x mode.val := by
  have high : ¬3≤|mode.val.1| := by rcases mode.property with one|two <;> omega
  have actual := represented mode.val
  simp only [sameCoupledXCoefficient,dif_neg high,dif_pos mode.property,pow_zero,Complex.ofReal_one,one_smul] at actual
  rw [lowIncomingTrace_apply]
  change (lower^(-(7/4:ℝ))*(Real.sqrt (lowMu length lower mode.val.2))⁻¹) •
    lowEnergySection lower length positive bounded field.ofLp.2 (1,mode) ⟨lower,le_rfl,bounded.le⟩=_
  rw [←lowPhysicalSection_x parameters lower length positive bounded field.ofLp.2 mode ⟨lower,le_rfl,bounded.le⟩,actual]
  rw [lambdaCircleCoefficient,←Complex.ofReal_inv,Complex.coe_smul,smul_smul,smul_smul]
  congr 1
  unfold lambdaCircleWeight
  field_simp [(Real.exp_pos _).ne',(cellFrequency_pos mode.val.2).ne']

end Grad.OriginalPhysicalKernelUniqueness
