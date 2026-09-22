import AKBR14ExactOriginalHomogeneousOuterConsumer
import AKS4OwnIncomingRestrictionEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularRestriction
open Grad.AnnularLowEnergy Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (positiveLower : 0<lower) (positiveUpper : 0<upper) (bounded : upper<1)
    (lengthPositive : 0<length) (included : lower≤upper)
    (field : CoupledSpace lower length positiveLower lengthPositive)
    (radius : Icc upper (1:ℝ)) (mode : ℤ×ℤ)

/-- Exact original physical Xi coefficients survive the SAME completed
endpoint restriction, including both high and low sectors. -/
theorem originalXiCoefficient_restrict :
    sameCoupledXiCoefficient parameters upper length positiveUpper bounded lengthPositive
      (coupledEndpointRestriction lower upper length positiveLower positiveUpper bounded lengthPositive included field) 0 radius mode=
    sameCoupledXiCoefficient parameters lower length positiveLower (included.trans_lt bounded) lengthPositive field 0
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  by_cases high : 3≤|mode.1|
  · simp only [sameCoupledXiCoefficient,dif_pos high,pow_zero,Complex.ofReal_one,one_smul]
    exact highEnergyRestriction_physical lower upper length positiveLower positiveUpper bounded included parameters field.ofLp.1.ofLp.1 ⟨mode,high⟩ radius
  · by_cases low : |mode.1|=1 ∨ |mode.1|=2
    · simp only [sameCoupledXiCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
      exact lowEnergyRestriction_physical parameters lower upper length included positiveLower positiveUpper bounded field.ofLp.2 (0,⟨mode,low⟩) radius
    · simp only [sameCoupledXiCoefficient,dif_neg high,dif_neg low]

/-- Exact original physical x=Rp coefficients survive that SAME restriction. -/
theorem originalXCoefficient_restrict :
    sameCoupledXCoefficient parameters upper length positiveUpper bounded lengthPositive
      (coupledEndpointRestriction lower upper length positiveLower positiveUpper bounded lengthPositive included field) 0 radius mode=
    sameCoupledXCoefficient parameters lower length positiveLower (included.trans_lt bounded) lengthPositive field 0
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  by_cases high : 3≤|mode.1|
  · simp only [sameCoupledXCoefficient,dif_pos high,pow_zero,Complex.ofReal_one,one_smul]
    exact highOmegaRestriction_physical lower upper length positiveLower positiveUpper bounded lengthPositive included parameters field.ofLp.1.ofLp.2 ⟨mode,high⟩ radius
  · by_cases low : |mode.1|=1 ∨ |mode.1|=2
    · simp only [sameCoupledXCoefficient,dif_neg high,dif_pos low,pow_zero,Complex.ofReal_one,one_smul]
      exact lowEnergyRestriction_physical parameters lower upper length included positiveLower positiveUpper bounded field.ofLp.2 (1,⟨mode,low⟩) radius
    · simp only [sameCoupledXCoefficient,dif_neg high,dif_neg low]

end Grad.OriginalPhysicalKernelUniqueness
