import AKDH2ActualCofactorEulerJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness Grad.GaugeCoefficients.Physical.Allocation
attribute [local irreducible] fullKernelSmul polynomialKernelAction

def ActualEulerFamily.smul {parameters : PhaseParameters} {L compact : ℝ} {source target : ℕ}
    {base : (state : AnnularReconstructionState parameters L compact) →
      (radius : RadialPoint) → RadialKernel parameters radius source target}
    (family : ActualEulerFamily parameters L compact base) (scalar : ℂ) :
    ActualEulerFamily parameters L compact (fun state radius => fullKernelSmul scalar (base state radius)) where
  kernels state rank radius := fullKernelSmul scalar (family.kernels state rank radius)
  zero state radius := by rw [family.zero]
  derivative state lower positive bounded := by
    apply kernelEulerTower_of_realization parameters lower positive bounded.le
      (fun rank radius => fullKernelSmul scalar (family.kernels state rank radius))
      (fun rank point => scalar • radialPolynomialAction parameters lower positive bounded.le (family.kernels state rank) 0 point)
      (fun rank point => polynomialKernelAction_smul
        (radialKernelParameters parameters (collarRadius lower positive bounded.le point)) 0 scalar
        (family.kernels state rank (collarRadius lower positive bounded.le point)))
    intro rank radius inside
    rw [smul_comm]
    exact (family.derivative state lower positive bounded rank radius inside).const_smul scalar
  moments := by
    intro rank moment
    obtain ⟨constant,nonnegative,bound⟩ := family.moments rank moment
    refine ⟨‖scalar‖*constant,mul_nonneg (norm_nonneg _) nonnegative,?_⟩
    intro state low radius
    exact (fullKernelSmul_moment_le scalar _ moment).trans
      ((mul_le_mul_of_nonneg_left (bound state low radius) (norm_nonneg scalar)).trans_eq (mul_assoc _ _ _).symm)

/-- D(r)=r at every rank: the literal radius factor in the original
physical flux has uniform Euler derivatives, including collar endpoints. -/
def fixedRadiusEulerFamily {source target : ℕ} (parameters : PhaseParameters) (L compact : ℝ)
    (family : (phase : PhaseParameters) → FullTwoFrequencyKernel phase source target)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    ActualEulerFamily parameters L compact (fun _ radius =>
      fullKernelSmul (radius.val : ℂ) (family (radialKernelParameters parameters radius))) := by
  let kernels := fun (_ : AnnularReconstructionState parameters L compact) (_ : ℕ) (radius : RadialPoint) =>
    fullKernelSmul (radius.val : ℂ) (family (radialKernelParameters parameters radius))
  refine ⟨kernels,(fun _ _ => rfl),?_,?_⟩
  · intro state lower positive bounded rank radius inside
    let operator := polynomialKernelAction parameters 0 (family parameters)
    have realization (point : ℝ) : radialPolynomialAction parameters lower positive bounded.le (kernels state rank) 0 point =
        (collarRadius lower positive bounded.le point).val • operator := by
      change polynomialKernelAction _ 0 (fullKernelSmul _ _) = _
      rw [polynomialKernelAction_real_smul]
      rw [polynomialKernelAction_congr _ parameters 0 _ _ (same _ _)]
    have nextSame : radialPolynomialAction parameters lower positive bounded.le (kernels state (rank+1)) 0 radius =
        radius • operator := by rw [show kernels state (rank+1) = kernels state rank by rfl,realization,collarRadius_literal _ _ _ _ inside]
    change HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded.le (kernels state rank) 0)
      (radius⁻¹ • radialPolynomialAction parameters lower positive bounded.le (kernels state (rank+1)) 0 radius) (Icc lower 1) radius
    rw [nextSame,smul_smul,inv_mul_cancel₀ (positive.trans_le inside.1).ne',one_smul]
    have derivative := (hasDerivWithinAt_id radius (Icc lower 1)).smul_const operator
    simp only [one_smul] at derivative
    apply derivative.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with point member
      rw [realization,collarRadius_literal _ _ _ _ member]
      rfl
    · rw [realization,collarRadius_literal _ _ _ _ inside]
      rfl
  · intro rank moment
    let constant := fullKernelMoment (maximalKernelParameters parameters) moment (family (maximalKernelParameters parameters))
    refine ⟨constant,fullKernelMoment_nonnegative _ _ _,?_⟩
    intro state _ radius
    apply (fullKernelSmul_moment_le (radius.val : ℂ) _ moment).trans
    have radiusBound : ‖(radius.val : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg radius.property.1] using radius.property.2
    have bounded := mul_le_mul_of_nonneg_right radiusBound (fullKernelMoment_nonnegative _ moment (family (radialKernelParameters parameters radius)))
    rw [one_mul] at bounded
    apply (bounded.trans (SameKernelEntries.radialMoment_le parameters radius moment (same _ _))).trans
    exact le_mul_of_one_le_right (fullKernelMoment_nonnegative _ _ _)
      (by linarith [physicalBudget_nonnegative parameters state.val.field state.val.rho state.val.epsilon (10+(rank+moment))])

end Grad.OriginalCartesianTameEstimate
