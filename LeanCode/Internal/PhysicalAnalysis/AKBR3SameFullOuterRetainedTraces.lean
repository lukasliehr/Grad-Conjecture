import AKBR2SameHighOuterPhysicalTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives
open Grad.AnnularForwardTraces Grad.AnnularPhysicalSolution Grad.AnnularStrongData Grad.AnnularSourceGraph
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularCurrentBoundary
open Grad.AnnularCurrentSource Grad.AnnularSmoothCore Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.AnnularLowEnergy
open Grad.AnnularUniformBoundary
open Grad.AnnularTiltedReference Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0<lower)
    (lowerHalf : lower≤1/2) (lengthPositive : 0<length)
    (candidate : CoupledSpace lower length positive lengthPositive)

def originalOuterX : NegativeTrace parameters 0 0 1 :=
  (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate).val+
    lowOuterXNegative parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2

def originalOuterXi : PositiveTrace parameters 0 0 1 :=
  actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1+
    lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2

/-- The full x trace includes every original nonzero angular mode. -/
theorem originalOuterX_physical (mode : ℤ×ℤ) :
    negativeTraceCoefficient parameters 0 0 (originalOuterX parameters lower length positive lowerHalf lengthPositive candidate) mode=
      sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive candidate 0
        ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩ mode := by
  rw [originalOuterX,negativeTraceCoefficient_add]
  by_cases high : 3≤|mode.1|
  · have outside : ¬(|mode.1|=1∨|mode.1|=2) := by omega
    have lowZero : negativeTraceCoefficient parameters 0 0
        (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2) mode=0 := by
      rw [negativeTraceCoefficient,lowOuterXNegative_outside parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2 mode outside,smul_zero]
    rw [lowZero,add_zero,originalHighOuterX_physical parameters lower length positive lowerHalf lengthPositive candidate ⟨mode,high⟩]
    simp only [sameCoupledXCoefficient,dif_pos high,highPowerCurve_physical lower highTiltExponent positive 1
      ⟨lowerHalf.trans (by norm_num),le_rfl⟩,Real.one_rpow,pow_zero,Complex.ofReal_one,one_smul]
  · have highZero := (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate).property mode (lt_of_not_ge high)
    rw [highZero,zero_add]
    by_cases low : |mode.1|=1∨|mode.1|=2
    · rw [lowOuterXNegative_physical parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2 ⟨mode,low⟩]
      simp only [sameCoupledXCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
    · rw [negativeTraceCoefficient,lowOuterXNegative_outside parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2 mode low,smul_zero]
      simp only [sameCoupledXCoefficient,dif_neg high,dif_neg low]

/-- The full Xi trace includes every original nonzero angular mode. -/
theorem originalOuterXi_physical (mode : ℤ×ℤ) :
    positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode=
      sameCoupledXiCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive candidate 0
        ⟨1,lowerHalf.trans (by norm_num),le_rfl⟩ mode := by
  have add : positiveTraceCoefficient parameters 0 0 (originalOuterXi parameters lower length positive lowerHalf lengthPositive candidate) mode=
      positiveTraceCoefficient parameters 0 0
        (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1) mode+
      positiveTraceCoefficient parameters 0 0
        (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2) mode := by
    change (positiveTraceWeight parameters 0 0 mode:ℂ)⁻¹ •
      (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1 mode+
        lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2 mode)=_
    exact smul_add _ _ _
  rw [add]
  by_cases high : 3≤|mode.1|
  · have outside : ¬(|mode.1|=1∨|mode.1|=2) := by omega
    have lowZero : positiveTraceCoefficient parameters 0 0
        (lowOuterXiPositive parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2) mode=0 := by
      rw [positiveTraceCoefficient,lowOuterXiPositive_outside parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2 mode outside,smul_zero]
    rw [lowZero,add_zero,originalHighOuterXi_physical parameters lower length positive lowerHalf lengthPositive candidate ⟨mode,high⟩]
    simp only [sameCoupledXiCoefficient,dif_pos high,highPowerCurve_physical lower highTiltExponent positive 1
      ⟨lowerHalf.trans (by norm_num),le_rfl⟩,Real.one_rpow,pow_zero,Complex.ofReal_one,one_smul]
  · have highZero : positiveTraceCoefficient parameters 0 0
        (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1) mode=0 := by
      rw [positiveTraceCoefficient,actualCurrentHighOuterTrace_low parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1 mode high,smul_zero]
    rw [highZero,zero_add]
    by_cases low : |mode.1|=1∨|mode.1|=2
    · rw [lowOuterXiPositive_physical parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2 ⟨mode,low⟩]
      simp only [sameCoupledXiCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
    · rw [positiveTraceCoefficient,lowOuterXiPositive_outside parameters lower length lengthPositive positive lowerHalf candidate.ofLp.2 mode low,smul_zero]
      simp only [sameCoupledXiCoefficient,dif_neg high,dif_neg low]

end Grad.OriginalKernelOuterUniqueness
