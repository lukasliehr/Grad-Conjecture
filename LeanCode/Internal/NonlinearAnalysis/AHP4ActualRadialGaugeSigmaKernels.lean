import AHP3ActualRadialForceKernels

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.AnnularReconstruction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.BoundaryKernelAction Grad.ActualCurrentPrimitives
open Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)

def radialGaugeCoefficients (kind : Fin 2) (component : Fin 3) (radial : ℕ) :
    ℤ × ℤ → ℂ :=
  gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
    state.data.parameter state.data.epsilon state.data.field state.low kind component radial r.val

theorem radialGaugeCoefficients_moments (kind : Fin 2) (component : Fin 3)
    (radial moment : ℕ) :
    Summable (productMoment parameters moment r.val
      (radialGaugeCoefficients parameters L compact state r kind component radial)) :=
  gaugeScalarMoment_summable parameters L state.data.rho state.data.alpha state.data.delta
    state.data.parameter state.data.epsilon state.data.field state.low kind component moment
    radial r.val r.property.1 r.property.2

def radialGaugeKernel (kind : Fin 2) (radial : ℕ) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3
    (fun component => radialGaugeCoefficients parameters L compact state r kind component radial)
    (fun component moment => radialGaugeCoefficients_moments parameters L compact state r
      kind component radial moment)

def radialGaugeRowsKernel (radial : ℕ) : RadialKernel parameters r 3 2 :=
  radialMatrixKernel parameters r 3 2
    (fun kind component => radialGaugeCoefficients parameters L compact state r kind component radial)
    (fun kind component moment => radialGaugeCoefficients_moments parameters L compact state r
      kind component radial moment)

def radialRotatedGaugeKernel (kind : Fin 2) (radial : ℕ) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3
    (fun component => angularCoefficientSequence
      (radialGaugeCoefficients parameters L compact state r kind component radial))
    (fun component moment => angularCoefficientSequence_moment_summable parameters moment r.val _
      (radialGaugeCoefficients_moments parameters L compact state r kind component radial (moment + 1)))

theorem radialGaugeCoefficients_bound (kind : Fin 2) (component : Fin 3)
    (radial moment : ℕ) :
    (∑' shift, productMoment parameters moment r.val
      (radialGaugeCoefficients parameters L compact state r kind component radial) shift) ≤
      gaugeScalarConstant parameters L compact kind component moment radial *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon
          (moment + radial + 5) :=
  gaugeScalarMoment_bound parameters L state.data.rho state.data.alpha state.data.delta
    state.data.parameter state.data.epsilon state.data.field state.low compact kind component
    moment radial r.val r.property.1 r.property.2 state.compactNonnegative state.alphaSmall
    state.deltaSmall state.parameterSmall

theorem radialGaugeRowsKernel_moment_le (radial moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment
        (radialGaugeRowsKernel parameters L compact state r radial) ≤
      (Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        ∑ kind, ∑ component, gaugeScalarConstant parameters L compact kind component moment radial) *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon
            (moment + radial + 5) := by
  apply (radialMatrixKernel_moment_le parameters r 3 2 moment _ _).trans
  have summed := Finset.sum_le_sum (s := Finset.univ) fun kind _ =>
    Finset.sum_le_sum (s := Finset.univ) fun component _ =>
      radialGaugeCoefficients_bound parameters L compact state r kind component radial moment
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  simp only [← Finset.sum_mul]
  ring

def radialSigmaCoefficients (component : Fin 3) (radial : ℕ) : ℤ × ℤ → ℂ :=
  sigmaScalar parameters L state.data.rho state.data.epsilon state.data.field state.low
    component radial r.val

theorem radialSigmaCoefficients_moments (component : Fin 3) (radial moment : ℕ) :
    Summable (productMoment parameters moment r.val
      (radialSigmaCoefficients parameters L compact state r component radial)) :=
  sigmaScalarMoment_summable parameters L state.data.rho state.data.epsilon state.data.field
    state.low component moment radial r.val r.property.1 r.property.2

def radialSigmaKernel (radial : ℕ) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3
    (fun component => radialSigmaCoefficients parameters L compact state r component radial)
    (fun component moment => radialSigmaCoefficients_moments parameters L compact state r
      component radial moment)

def radialRotatedSigmaKernel (radial : ℕ) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3
    (fun component => angularCoefficientSequence
      (radialSigmaCoefficients parameters L compact state r component radial))
    (fun component moment => angularCoefficientSequence_moment_summable parameters moment r.val _
      (radialSigmaCoefficients_moments parameters L compact state r component radial (moment + 1)))

theorem radialSigmaCoefficients_bound (component : Fin 3) (radial moment : ℕ) :
    (∑' shift, productMoment parameters moment r.val
      (radialSigmaCoefficients parameters L compact state r component radial) shift) ≤
      sigmaScalarConstant parameters L component moment radial *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon
          (moment + radial + 5) :=
  sigmaScalarMoment_bound parameters L state.data.rho state.data.epsilon state.data.field
    state.low component moment radial r.val r.property.1 r.property.2

theorem radialSigmaKernel_moment_le (radial moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment
        (radialSigmaKernel parameters L compact state r radial) ≤
      (Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        ∑ component, sigmaScalarConstant parameters L component moment radial) *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon
            (moment + radial + 5) := by
  apply (radialRowKernel_moment_le parameters r 3 moment _ _).trans
  have summed := Finset.sum_le_sum (s := Finset.univ) fun component _ =>
    radialSigmaCoefficients_bound parameters L compact state r component radial moment
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  simp only [← Finset.sum_mul]
  ring

theorem radialGaugeKernel_one_entry (kind : Fin 2) (shift input : ℤ × ℤ) :
    (radialGaugeKernel parameters L compact state ⟨1, zero_le_one, le_rfl⟩ kind 0).entry
        shift input =
      (actualGaugeBoundaryKernel parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low kind).entry shift input := rfl

theorem radialSigmaKernel_one_entry (shift input : ℤ × ℤ) :
    (radialSigmaKernel parameters L compact state ⟨1, zero_le_one, le_rfl⟩ 0).entry shift input =
      (actualSigmaBoundaryKernel parameters L state.data.rho state.data.epsilon
        state.data.field state.low).entry shift input := rfl

end Grad.AnnularReconstruction
