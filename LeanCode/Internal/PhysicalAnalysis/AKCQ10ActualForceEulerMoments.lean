import AKCQ9RawEulerKernelMoments
import AJH10ActualPrimitiveSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness
open Grad.ActualCurrentPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- All actual ordinary radial matrix jets, with no new coefficient field. -/
def actualForceMatrixJets (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (kind : Fin 2)
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) :
    ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 1 :=
  rowMultiplicationEntry 3 (fun component => forceScalar parameters L state.data.rho state.data.epsilon
    state.data.field kind state.low component rank radius) shift input

theorem actualForceMatrixJets_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (kind : Fin 2)
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) :
    HasDerivAt (fun point => actualForceMatrixJets parameters L compact state kind rank point shift input)
      (actualForceMatrixJets parameters L compact state kind (rank+1) radius shift input) radius :=
  rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => actualForceScalar_hasDerivAt parameters L compact state kind component rank point mode)
    radius shift input

def actualForceEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (kind : Fin 2)
    (radius : RadialPoint) : ℕ → RadialKernel parameters radius 3 1
  | 0 => radialForceKernel parameters L compact state radius kind 0
  | rank+1 => rawEulerKernel radius (fun raw => radialForceKernel parameters L compact state radius kind raw)
      (positiveEulerTerms rank)

def actualForceRawMomentConstant (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (moment raw : ℕ) : ℝ :=
  3 * Real.exp (parameters.sigma0+2*parameters.gamma) * forceFourierConstant parameters L kind moment raw

def actualForceEulerMomentConstant (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (moment : ℕ) : ℕ → ℝ
  | 0 => actualForceRawMomentConstant parameters L kind moment 0
  | rank+1 => rawEulerMomentConstant (actualForceRawMomentConstant parameters L kind moment) (positiveEulerTerms rank)

theorem actualForceRawMomentConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (moment raw : ℕ) :
    0 ≤ actualForceRawMomentConstant parameters L kind moment raw :=
  mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (forceFourierConstant_pos parameters L kind moment raw).le

theorem actualForceEulerMomentConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (moment rank : ℕ) :
    0 ≤ actualForceEulerMomentConstant parameters L kind moment rank := by
  cases rank with
  | zero => exact actualForceRawMomentConstant_nonnegative parameters L kind moment 0
  | succ rank =>
      exact rawEulerMomentConstant_nonnegative _
        (actualForceRawMomentConstant_nonnegative parameters L kind moment) _

/-- The kernel is the actual Euler derivative of the original force matrix,
including the axis and every input cell. -/
theorem actualForceEulerKernel_entry (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact) (kind : Fin 2)
    (radius : RadialPoint) (rank : ℕ) (shift input : ℤ × ℤ) :
    (actualForceEulerKernel parameters L compact state kind radius rank).entry shift input =
      vectorEulerIteratedDerivative rank
        (fun point => actualForceMatrixJets parameters L compact state kind 0 point shift input) radius.val := by
  cases rank with
  | zero => rfl
  | succ rank =>
      exact rawEulerKernel_actual radius _
        (fun raw point => actualForceMatrixJets parameters L compact state kind raw point shift input)
        (fun raw point => actualForceMatrixJets_derivative parameters L compact state kind raw point shift input)
        shift input (fun _ => rfl) rank

/-- Sharp joint raw-Euler/displacement budget for the same original force.
The constant is independent of the state and radius; there is one high norm. -/
theorem actualForceEulerKernel_moment_bound (parameters : PhaseParameters) (L compact : ℝ)
    (kind : Fin 2) (rank moment : ℕ) (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (actualForceEulerKernel parameters L compact state kind radius rank) ≤
      actualForceEulerMomentConstant parameters L kind moment rank *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+rank+6) := by
  cases rank with
  | zero => exact radialForceKernel_moment_le parameters L compact state radius kind 0 moment
  | succ rank =>
      apply rawEulerKernel_moment_bound
      intro term member
      have rawBound := radialForceKernel_moment_le parameters L compact state radius kind (term.1+1) moment
      have ordered := positiveEulerTerms_rank rank term member
      exact rawBound.trans (mul_le_mul_of_nonneg_left
        (physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon (by omega))
        (actualForceRawMomentConstant_nonnegative parameters L kind moment (term.1+1)))

end Grad.OriginalCartesianTameEstimate
