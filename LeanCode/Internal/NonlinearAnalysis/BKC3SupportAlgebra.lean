import BKC2ActionCoefficients

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Ledger

theorem IsAngularConstant.sub {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {first second : NegativeTrace parameters angular cell dimension}
    (hfirst : IsAngularConstant parameters angular cell first)
    (hsecond : IsAngularConstant parameters angular cell second) :
    IsAngularConstant parameters angular cell (first - second) := by
  intro mode nonzero
  rw [negativeTraceCoefficient_sub, hfirst mode nonzero, hsecond mode nonzero, sub_zero]

theorem IsAngularMeanFree.add {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {first second : NegativeTrace parameters angular cell dimension}
    (hfirst : IsAngularMeanFree parameters angular cell first)
    (hsecond : IsAngularMeanFree parameters angular cell second) :
    IsAngularMeanFree parameters angular cell (first + second) := by
  intro axial
  rw [negativeTraceCoefficient_add, hfirst, hsecond, add_zero]

theorem IsAngularMeanFree.neg {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {field : NegativeTrace parameters angular cell dimension}
    (supported : IsAngularMeanFree parameters angular cell field) :
    IsAngularMeanFree parameters angular cell (-field) := by
  intro axial
  rw [negativeTraceCoefficient_neg, supported, neg_zero]

theorem IsAngularMeanFree.sub {dimension : ℕ}
    {parameters : PhaseParameters} {angular cell : ℕ}
    {first second : NegativeTrace parameters angular cell dimension}
    (hfirst : IsAngularMeanFree parameters angular cell first)
    (hsecond : IsAngularMeanFree parameters angular cell second) :
    IsAngularMeanFree parameters angular cell (first - second) := by
  simpa only [sub_eq_add_neg] using hfirst.add hsecond.neg

theorem EncodedSupport.add {parameters : PhaseParameters} {angular cell : ℕ}
    {first second : NegativeTrace parameters angular cell 3}
    (hfirst : EncodedSupport parameters angular cell first)
    (hsecond : EncodedSupport parameters angular cell second) :
    EncodedSupport parameters angular cell (first + second) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mode nonzero
    simp only [negativeTraceCoefficient_add, PiLp.add_apply, hfirst.1 mode nonzero,
      hsecond.1 mode nonzero, add_zero]
  · intro axial
    simp only [negativeTraceCoefficient_add, PiLp.add_apply, hfirst.2.1 axial,
      hsecond.2.1 axial, add_zero]
  · intro axial
    simp only [negativeTraceCoefficient_add, PiLp.add_apply, hfirst.2.2 axial,
      hsecond.2.2 axial, add_zero]

theorem EncodedSupport.neg {parameters : PhaseParameters} {angular cell : ℕ}
    {field : NegativeTrace parameters angular cell 3}
    (supported : EncodedSupport parameters angular cell field) :
    EncodedSupport parameters angular cell (-field) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mode nonzero
    simp only [negativeTraceCoefficient_neg, PiLp.neg_apply, supported.1 mode nonzero,
      neg_zero]
  · intro axial
    simp only [negativeTraceCoefficient_neg, PiLp.neg_apply, supported.2.1 axial,
      neg_zero]
  · intro axial
    simp only [negativeTraceCoefficient_neg, PiLp.neg_apply, supported.2.2 axial,
      neg_zero]

theorem EncodedSupport.sub {parameters : PhaseParameters} {angular cell : ℕ}
    {first second : NegativeTrace parameters angular cell 3}
    (hfirst : EncodedSupport parameters angular cell first)
    (hsecond : EncodedSupport parameters angular cell second) :
    EncodedSupport parameters angular cell (first - second) := by
  simpa only [sub_eq_add_neg] using hfirst.add hsecond.neg

theorem angularMeanKernel_action_constant {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) :
    IsAngularConstant parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (angularMeanKernel parameters dimension) field) := by
  intro mode nonzero
  rw [angularMeanKernel, scalarModeDiagonalKernel_action_coefficient]
  simp only [angularMeanMultiplier, if_neg nonzero, zero_smul]

theorem angularMeanFreeKernel_action_meanFree {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) :
    IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (angularMeanFreeKernel parameters dimension) field) := by
  intro axial
  rw [angularMeanFreeKernel, scalarModeDiagonalKernel_action_coefficient]
  simp only [angularMeanFreeMultiplier, ite_true, zero_smul]

theorem angularInverseKernel_action_meanFree {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) :
    IsAngularMeanFree parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (angularInverseKernel parameters dimension) field) := by
  intro axial
  rw [angularInverseKernel, scalarModeDiagonalKernel_action_coefficient]
  simp only [angularInverseMultiplier, ite_true, zero_smul]

theorem coordinateInjectionKernel_action_encoded_zero
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 1)
    (supported : IsAngularConstant parameters angular cell field) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (coordinateInjectionKernel parameters 3 0) field) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mode nonzero
    simp only [coordinateInjectionKernel_action_coefficient, ite_true,
      supported mode nonzero, PiLp.zero_apply]
  · intro axial
    simp [coordinateInjectionKernel_action_coefficient]
  · intro axial
    simp [coordinateInjectionKernel_action_coefficient, Fin.ext_iff]

theorem coordinateInjectionKernel_action_encoded_one
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell field) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (coordinateInjectionKernel parameters 3 1) field) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mode _
    simp [coordinateInjectionKernel_action_coefficient]
  · intro axial
    simp only [coordinateInjectionKernel_action_coefficient, ite_true,
      supported axial, PiLp.zero_apply]
  · intro axial
    simp [coordinateInjectionKernel_action_coefficient, Fin.ext_iff]

theorem coordinateInjectionKernel_action_encoded_two
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 1)
    (supported : IsAngularMeanFree parameters angular cell field) :
    EncodedSupport parameters angular cell
      (fullNegativeKernelAction parameters angular cell
        (coordinateInjectionKernel parameters 3 2) field) := by
  refine ⟨?_, ?_, ?_⟩
  · intro mode _
    simp [coordinateInjectionKernel_action_coefficient, Fin.ext_iff]
  · intro axial
    simp [coordinateInjectionKernel_action_coefficient, Fin.ext_iff]
  · intro axial
    simp only [coordinateInjectionKernel_action_coefficient, ite_true,
      supported axial, PiLp.zero_apply]

theorem componentModeKernel_action_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ) (coordinate : Fin dimension)
    (multiplier : ℤ × ℤ → ℂ) (bound : ℝ)
    (bounded : ∀ mode, ‖multiplier mode‖ ≤ bound)
    (field : NegativeTrace parameters angular cell dimension) (mode : ℤ × ℤ)
    (output : Fin dimension) :
    negativeTraceCoefficient parameters angular cell
        (fullNegativeKernelAction parameters angular cell
          (componentModeKernel parameters dimension coordinate multiplier bound bounded)
          field) mode output =
      if output = coordinate then multiplier mode *
        negativeTraceCoefficient parameters angular cell field mode coordinate else 0 := by
  simp only [componentModeKernel, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, coordinateInjectionKernel_action_coefficient,
    scalarModeDiagonalKernel_action_coefficient, PiLp.smul_apply, smul_eq_mul,
    coordinateProjectionKernel_action_coefficient]

end Grad.BoundaryKernelAction
