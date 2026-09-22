import AHP20GenuineRadialAngularReconstruction

noncomputable section
set_option maxHeartbeats 1600000

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

theorem radialSigmaKernel_derivative (angular cell : ℕ)
    (input derivative : NegativeTrace (rp parameters r) angular cell 3)
    (differentiated : IsAngularDerivative (rp parameters r) angular cell input derivative) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialSigmaKernel parameters L compact state r 0) input)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialRotatedSigmaKernel parameters L compact state r 0) input +
       fullNegativeKernelAction (rp parameters r) angular cell
        (radialSigmaKernel parameters L compact state r 0) derivative) :=
  boundaryRowMultiplicationKernel_derivative (rp parameters r) angular cell 3 _
    (fun component moment => by
      simpa only [radialKernelProductMoment] using
        radialSigmaCoefficients_moments parameters L compact state r component 0 moment)
    (fun component moment => by
      simpa only [radialKernelProductMoment] using
        angularCoefficientSequence_moment_summable parameters moment r.val _
          (radialSigmaCoefficients_moments parameters L compact state r component 0 (moment + 1)))
    input derivative differentiated

theorem radialSigmaComponentKernel_derivative (component : Fin 3) (angular cell : ℕ)
    (input derivative : NegativeTrace (rp parameters r) angular cell 1)
    (differentiated : IsAngularDerivative (rp parameters r) angular cell input derivative) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialSigmaComponentKernel parameters L compact state r component) input)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialRotatedSigmaComponentKernel parameters L compact state r component) input +
       fullNegativeKernelAction (rp parameters r) angular cell
        (radialSigmaComponentKernel parameters L compact state r component) derivative) := by
  apply fullNegativeKernelAction_derivative _ _ _ _ _ _ input derivative differentiated
  intro shift frequency
  unfold radialRotatedSigmaComponentKernel radialSigmaComponentKernel radialScalarKernel
  rw [boundaryScalarMultiplicationKernel_entry, boundaryScalarMultiplicationKernel_entry]
  unfold angularCoefficientSequence
  rw [smul_smul]

variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialUnknownVKernel_first (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 1) :
    fullNegativeKernelAction (rp parameters r) angular cell (coordinateProjectionKernel (rp parameters r) 3 0)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialUnknownVKernel parameters L compact state r small) input) = input := by
  apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
  intro mode
  apply PiLp.ext
  intro coordinate
  have unique : coordinate = 0 := Fin.eq_zero coordinate
  subst coordinate
  rw [coordinateProjectionKernel_action_coefficient]
  unfold radialUnknownVKernel
  rw [fullNegativeKernelAction_add, negativeTraceCoefficient_add]
  simp only [PiLp.add_apply, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    encodedRotationKernel_first_coefficient, firstCoordinateInjectionKernel,
    coordinateInjectionKernel_action_coefficient, ite_true, zero_add]

theorem radialKnownRAStarKernel_first (angular cell : ℕ)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    fullNegativeKernelAction (rp parameters r) angular cell (coordinateProjectionKernel (rp parameters r) 3 0)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownRAStarKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)) = 0 := by
  apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
  intro mode
  apply PiLp.ext
  intro coordinate
  have unique : coordinate = 0 := Fin.eq_zero coordinate
  subst coordinate
  rw [coordinateProjectionKernel_action_coefficient]
  unfold radialKnownRAStarKernel radialKnownRotatedQStarKernel
  rw [fullNegativeKernelAction_add, negativeTraceCoefficient_add]
  simp only [PiLp.add_apply, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    encodedRotationKernel_first_coefficient, secondCoordinateInjectionKernel,
    coordinateInjectionKernel_action_coefficient, zero_add]
  simp [negativeTraceCoefficient]

end Grad.AnnularReconstruction
