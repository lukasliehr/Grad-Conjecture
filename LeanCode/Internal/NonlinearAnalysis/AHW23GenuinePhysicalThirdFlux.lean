import AHW22LiteralCircularEntries

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

/-- The actual AH25 b3 before differentiation, using the third signed cofactor row. -/
def radialNormalizedBThreeKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelAdd
    (fullKernelComposition (radialSignedCofactorRowKernel parameters L compact state 2 r)
      (radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property))
    (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 2 r)
      (sevenInputSlotKernel (radialKernelParameters parameters r) 3))

theorem sevenInputSlotKernel_flatten (parameters : PhaseParameters) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell) (slot : Fin 7) :
    fullNegativeKernelAction parameters angular cell (sevenInputSlotKernel parameters slot)
      (sevenSlotFlatten parameters angular cell input) = input slot := by
  apply NegativeTrace.ext_coefficient parameters angular cell
  intro mode
  apply PiLp.ext
  intro coordinate
  have unique := Fin.eq_zero coordinate
  subst coordinate
  simp only [sevenInputSlotKernel, coordinateProjectionKernel_action_coefficient, sevenSlotFlatten_coefficient]

/-- Genuine angular derivative of the same b3, without a high projection premise. -/
theorem radialNormalizedBThreeKernel_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell)
    (supported : IsAngularMeanFree (radialKernelParameters parameters r) angular cell (input 0))
    (scalarDerivative : IsAngularDerivative (radialKernelParameters parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (radialKernelParameters parameters r) angular cell
      (fullNegativeKernelAction _ angular cell (radialNormalizedBThreeKernel parameters L compact state r)
        (sevenSlotFlatten _ angular cell input))
      (fullNegativeKernelAction _ angular cell (radialNormalizedUnprojectedCKernel parameters L compact state r)
        (sevenSlotFlatten _ angular cell input)) := by
  have covariantDerivative := radialNormalizedCovariantKernel_derivative parameters L compact state.val.val r
    state.val.property angular cell input supported scalarDerivative
  have row := radialSignedCofactorRowKernel_derivative parameters L compact state 2 r angular cell _ _ covariantDerivative
  have component := radialSignedCofactorComponentKernel_derivative parameters L compact state 1 2 r angular cell _ _ scalarDerivative
  have combined := row.add component
  convert combined using 1
  · simp only [radialNormalizedBThreeKernel, fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
      ContinuousLinearMap.comp_apply, sevenInputSlotKernel_flatten]
  · simp only [radialNormalizedUnprojectedCKernel, fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
      ContinuousLinearMap.comp_apply, sevenInputSlotKernel_flatten]
    abel

/-- Therefore the previously constructed high c is exactly Q Rb3. -/
theorem radialNormalizedCKernel_genuineDerivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell)
    (supported : IsAngularMeanFree (radialKernelParameters parameters r) angular cell (input 0))
    (scalarDerivative : IsAngularDerivative (radialKernelParameters parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (radialKernelParameters parameters r) angular cell
      (fullNegativeKernelAction _ angular cell (highAngularKernel (radialKernelParameters parameters r) 1)
        (fullNegativeKernelAction _ angular cell (radialNormalizedBThreeKernel parameters L compact state r)
          (sevenSlotFlatten _ angular cell input)))
      (fullNegativeKernelAction _ angular cell (radialNormalizedCKernel parameters L compact state r)
        (sevenSlotFlatten _ angular cell input)) := by
  simpa only [radialNormalizedCKernel_projected, highAngularKernel, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply] using
    (radialNormalizedBThreeKernel_derivative parameters L compact state r angular cell input supported scalarDerivative).scalarMode
      highAngularMultiplier 1 highAngularMultiplier_norm_le

end Grad.AnnularReconstruction
