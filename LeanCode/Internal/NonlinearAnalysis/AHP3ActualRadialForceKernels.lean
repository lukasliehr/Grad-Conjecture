import AHP2OriginalRadialCoefficientState

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.AnnularReconstruction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.BoundaryKernelAction Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)

def radialForceKernel (kind : Fin 2) (radial : ℕ) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3
    (fun component => forceScalar parameters L state.data.rho state.data.epsilon
      state.data.field kind state.low component radial r.val)
    (fun component moment => forceScalarMoment_summable parameters L state.data.rho
      state.data.epsilon state.data.field kind state.low component moment radial r.val
      r.property.1 r.property.2)

def radialRotatedForceKernel (kind : Fin 2) (radial : ℕ) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3
    (fun component => angularCoefficientSequence
      (forceScalar parameters L state.data.rho state.data.epsilon
        state.data.field kind state.low component radial r.val))
    (fun component moment => (rotatedForceScalarMoment_bound parameters L state.data.rho
      state.data.epsilon state.data.field kind state.low component moment radial r.val
      r.property.1 r.property.2).1)

theorem radialForceKernel_moment_le (kind : Fin 2) (radial moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment
        (radialForceKernel parameters L compact state r kind radial) ≤
      3 * Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        forceFourierConstant parameters L kind moment radial *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon
            (moment + radial + 6) := by
  apply (radialRowKernel_moment_le parameters r 3 moment _ _).trans
  have each (component : Fin 3) := forceScalarMoment_bound parameters L state.data.rho
    state.data.epsilon state.data.field kind state.low component moment radial r.val
    r.property.1 r.property.2
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun component _ => each component)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  ring

theorem radialRotatedForceKernel_moment_le (kind : Fin 2) (radial moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment
        (radialRotatedForceKernel parameters L compact state r kind radial) ≤
      3 * Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
        forceFourierConstant parameters L kind (moment + 1) radial *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon
            (moment + radial + 7) := by
  apply (radialRowKernel_moment_le parameters r 3 moment _ _).trans
  have each (component : Fin 3) := (rotatedForceScalarMoment_bound parameters L state.data.rho
    state.data.epsilon state.data.field kind state.low component moment radial r.val
    r.property.1 r.property.2).2
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun component _ => each component)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
  apply (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq
  ring

/-- Exact agreement with the accepted outer-circle force entry. -/
theorem radialForceKernel_one_entry (kind : Fin 2) (shift input : ℤ × ℤ) :
    (radialForceKernel parameters L compact state ⟨1, zero_le_one, le_rfl⟩ kind 0).entry
        shift input =
      (actualForceBoundaryKernel parameters L state.data.rho state.data.epsilon
        state.data.field kind state.low).entry shift input := rfl

/-- Exact agreement with the genuine accepted outer-circle R coefficient. -/
theorem radialRotatedForceKernel_one_entry (kind : Fin 2) (shift input : ℤ × ℤ) :
    (radialRotatedForceKernel parameters L compact state ⟨1, zero_le_one, le_rfl⟩ kind 0).entry
        shift input =
      (actualRotatedForceBoundaryKernel parameters L state.data.rho state.data.epsilon
        state.data.field kind state.low).entry shift input := rfl

end Grad.AnnularReconstruction
