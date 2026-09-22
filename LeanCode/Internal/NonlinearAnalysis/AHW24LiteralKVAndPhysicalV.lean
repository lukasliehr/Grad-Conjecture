import AHW23GenuinePhysicalThirdFlux

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

theorem angularMeanFreeAction_eq_sub_mean (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 1) :
    fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters 1) field =
      field - fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters 1) field := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  simp only [angularMeanFreeKernel, angularMeanKernel, scalarModeDiagonalKernel_action_coefficient,
    negativeTraceCoefficient_sub]
  by_cases zero : mode.1 = 0 <;> simp [angularMeanFreeMultiplier, angularMeanMultiplier, zero]

/-- Literal AD15: neither mean factor is commuted through a variable cofactor. -/
theorem radialKVKernel_meanExpansion (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (field : NegativeTrace (radialKernelParameters parameters r) angular cell 3) :
    let act := fun {i o : ℕ} (kernel : RadialKernel parameters r i o) =>
      fullNegativeKernelAction (radialKernelParameters parameters r) angular cell kernel
    act (radialKVKernel parameters L compact state r) field =
      (act (radialCofactorJetRowKernel parameters L compact state 1 0 1 r) field +
        act (radialSignedCofactorComponentKernel parameters L compact state 1 0 r)
          (act (radialRetainedForceKernel parameters L compact state.val.val r) field) +
        act (radialSignedCofactorComponentKernel parameters L compact state 1 1 r)
          (act (radialOriginalForceZeroKernel parameters L compact state r) field) -
        act (radialSignedCofactorComponentKernel parameters L compact state 1 2 r)
          (act (radialForceKernel parameters L compact state.val.val r 1 0) field)) -
      act (radialSignedCofactorComponentKernel parameters L compact state 1 0 r)
        (act (angularMeanKernel (radialKernelParameters parameters r) 1)
          (act (radialRetainedForceKernel parameters L compact state.val.val r) field)) +
      act (radialSignedCofactorComponentKernel parameters L compact state 1 2 r)
        (act (angularMeanKernel (radialKernelParameters parameters r) 1)
          (act (radialForceKernel parameters L compact state.val.val r 1 0) field)) := by
  dsimp only
  simp only [radialKVKernel, fullNegativeKernelAction_sub, fullNegativeKernelAction_add,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, angularMeanFreeAction_eq_sub_mean, map_sub]
  abel

/-- AH23 in the original physical coordinates (a,xi,Rxi), including its outer P. -/
def originalPhysicalVTrace (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (covariant : NegativeTrace (radialKernelParameters parameters r) angular cell 3)
    (xi rotatedXi : NegativeTrace (radialKernelParameters parameters r) angular cell 1) :
    NegativeTrace (radialKernelParameters parameters r) angular cell 1 :=
  let act := fun {i o : ℕ} (kernel : RadialKernel parameters r i o) =>
    fullNegativeKernelAction (radialKernelParameters parameters r) angular cell kernel
  act (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
    (((r.val : ℂ)⁻¹ * (r.val : ℂ)⁻¹) •
      act (radialSignedCofactorComponentKernel parameters L compact state 1 1 r) rotatedXi +
      (r.val : ℂ)⁻¹ • act (radialKVKernel parameters L compact state r) covariant -
      (r.val : ℂ)⁻¹ • act (radialCofactorJetComponentKernel parameters L compact state 1 0 1 0 r) xi -
      ((L : ℂ)⁻¹ * (r.val : ℂ)⁻¹) • act (radialCofactorJetComponentKernel parameters L compact state 1 2 0 2 r) xi)

/-- Exact normalized rV of the same original covariant reconstruction and original xi slots. -/
theorem radialNormalizedRVKernel_originalPhysical (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (positive : 0 < r.val) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell) :
    fullNegativeKernelAction _ angular cell (radialNormalizedRVKernel parameters L compact state r)
      (sevenSlotFlatten _ angular cell (radialNormalizedSevenInput parameters r angular cell input)) =
    (r.val : ℂ) • fullNegativeKernelAction _ angular cell (highAngularKernel (radialKernelParameters parameters r) 1)
      (originalPhysicalVTrace parameters L compact state r angular cell
        (fullNegativeKernelAction _ angular cell
          (radialCovariantKernel parameters L compact state.val.val r state.val.property positive)
          (sevenSlotFlatten _ angular cell input)) (input 3) (input 1)) := by
  have nonzero : (r.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  simp only [radialNormalizedRVKernel_projected, radialNormalizedUnprojectedRVKernel,
    fullNegativeKernelAction_comp, fullNegativeKernelAction_sub, fullNegativeKernelAction_add,
    fullNegativeKernelAction_smul, ContinuousLinearMap.comp_apply, 
    sevenInputSlotKernel_flatten,
    originalPhysicalVTrace, highAngular_action_meanFree_eq,
    radialCovariantKernel, radialSevenSlotKernel_action]
  simp only [radialNormalizedSevenInput, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, map_smul, map_add, map_sub, smul_add, smul_sub, smul_smul]
  simp only [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
  have axial : (r.val : ℂ) * (L : ℂ)⁻¹ * (r.val : ℂ)⁻¹ = (L : ℂ)⁻¹ := by
    rw [mul_right_comm, mul_inv_cancel₀ nonzero, one_mul]
  rw [axial]
  module

end Grad.AnnularReconstruction
