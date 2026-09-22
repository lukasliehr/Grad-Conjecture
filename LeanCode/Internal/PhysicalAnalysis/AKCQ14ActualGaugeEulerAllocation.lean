import AKCQ12SameForceSharpEulerSchurBound
import AJH10ActualPrimitiveSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness
open Grad.AnnularWeightedSmoothness
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

/-- All actual ordinary radial matrix jets, with no new coefficient field. -/
def actualGaugeMatrixJets (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) :
    ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 2 :=
  matrixMultiplicationEntry 3 2 (fun row component => gaugeScalar parameters L state.data.rho state.data.alpha
    state.data.delta state.data.parameter state.data.epsilon state.data.field state.low row component rank radius) shift input

theorem actualGaugeMatrixJets_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) :
    HasDerivAt (fun point => actualGaugeMatrixJets parameters L compact state rank point shift input)
      (actualGaugeMatrixJets parameters L compact state (rank+1) radius shift input) radius :=
  matrixMultiplicationEntry_hasDerivAt 3 2 _ _
    (fun row component point mode => gaugeScalar_hasDerivAt parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row component rank point mode) radius shift input

def actualGaugeEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) : ℕ → RadialKernel parameters radius 3 2
  | 0 => radialGaugeRowsKernel parameters L compact state radius 0
  | rank+1 => rawEulerKernel radius (fun raw => radialGaugeRowsKernel parameters L compact state radius raw)
      (positiveEulerTerms rank)

def actualGaugeRawMomentConstant (parameters : PhaseParameters) (L compact : ℝ)
    (moment raw : ℕ) : ℝ :=
  Real.exp (parameters.sigma0+2*parameters.gamma) * (∑ row : Fin 2, ∑ component : Fin 3, gaugeScalarConstant parameters L compact row component moment raw)

def actualGaugeEulerMomentConstant (parameters : PhaseParameters) (L compact : ℝ)
    (moment : ℕ) : ℕ → ℝ
  | 0 => actualGaugeRawMomentConstant parameters L compact moment 0
  | rank+1 => rawEulerMomentConstant (actualGaugeRawMomentConstant parameters L compact moment) (positiveEulerTerms rank)

theorem actualGaugeRawMomentConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ)
    (moment raw : ℕ) :
    0 ≤ actualGaugeRawMomentConstant parameters L compact moment raw :=
  mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun row _ => Finset.sum_nonneg (fun component _ => gaugeScalarConstant_nonnegative parameters L compact row component moment raw)))

theorem actualGaugeEulerMomentConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ)
    (moment rank : ℕ) :
    0 ≤ actualGaugeEulerMomentConstant parameters L compact moment rank := by
  cases rank with
  | zero => exact actualGaugeRawMomentConstant_nonnegative parameters L compact moment 0
  | succ rank =>
      exact rawEulerMomentConstant_nonnegative _
        (actualGaugeRawMomentConstant_nonnegative parameters L compact moment) _

/-- The kernel is the actual Euler derivative of the original gauge matrix,
including the axis and every input cell. -/
theorem actualGaugeEulerKernel_entry (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) (rank : ℕ) (shift input : ℤ × ℤ) :
    (actualGaugeEulerKernel parameters L compact state radius rank).entry shift input =
      vectorEulerIteratedDerivative rank
        (fun point => actualGaugeMatrixJets parameters L compact state 0 point shift input) radius.val := by
  cases rank with
  | zero => rfl
  | succ rank =>
      exact rawEulerKernel_actual radius _
        (fun raw point => actualGaugeMatrixJets parameters L compact state raw point shift input)
        (fun raw point => actualGaugeMatrixJets_derivative parameters L compact state raw point shift input)
        shift input (fun _ => rfl) rank

/-- Sharp joint raw-Euler/displacement budget for the same original gauge.
The constant is independent of the state and radius; there is one high norm. -/
theorem actualGaugeEulerKernel_moment_bound (parameters : PhaseParameters) (L compact : ℝ)
    (rank moment : ℕ) (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (actualGaugeEulerKernel parameters L compact state radius rank) ≤
      actualGaugeEulerMomentConstant parameters L compact moment rank *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+rank+5) := by
  cases rank with
  | zero => exact radialGaugeRowsKernel_moment_le parameters L compact state radius 0 moment
  | succ rank =>
      apply rawEulerKernel_moment_bound
      intro term member
      have rawBound := radialGaugeRowsKernel_moment_le parameters L compact state radius (term.1+1) moment
      have ordered := positiveEulerTerms_rank rank term member
      exact rawBound.trans (mul_le_mul_of_nonneg_left
        (physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon (by omega))
        (actualGaugeRawMomentConstant_nonnegative parameters L compact moment (term.1+1)))



def actualGaugeConjugatedEulerConstant (parameters : PhaseParameters) (L compact : ℝ)
    (rank moment : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (rank+1), (rank.choose index : ℝ) * positiveEulerRatioConstant parameters index *
    actualGaugeEulerMomentConstant parameters L compact (moment+index) (rank-index)

theorem actualGaugeConjugatedEulerConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ)
    (rank moment : ℕ) :
    0 ≤ actualGaugeConjugatedEulerConstant parameters L compact rank moment :=
  Finset.sum_nonneg (fun index _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters index)))
    (actualGaugeEulerMomentConstant_nonnegative parameters L compact (moment+index) (rank-index)))

/-- SAME actual gauge matrices, full original phase and every full cell.
Raw derivative rank and phase displacement rank are allocated jointly,
leaving exactly one physical budget at moment+rank+5. -/
theorem actualGaugeConjugatedEuler_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (rank moment : ℕ) (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) (positive : 0 < radius.val) (inputs : (ℤ × ℤ) → (ℤ × ℤ)) :
    Summable (fun (shift : ℤ × ℤ) => Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ moment *
      ‖actualConjugatedEulerEntry parameters (actualGaugeMatrixJets parameters L compact state 0)
        rank radius.val shift (inputs shift)‖) ∧
    actualEulerDisplacementMoment parameters (actualGaugeMatrixJets parameters L compact state 0)
      rank moment radius.val inputs ≤
        actualGaugeConjugatedEulerConstant parameters L compact rank moment *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+rank+5) := by
  have smooth (shift input : ℤ × ℤ) :
      ContDiff ℝ ∞ (fun point => actualGaugeMatrixJets parameters L compact state 0 point shift input) :=
    derivativeTower_smooth (fun raw point => actualGaugeMatrixJets parameters L compact state raw point shift input)
      (fun raw point => actualGaugeMatrixJets_derivative parameters L compact state raw point shift input) 0
  have allocated := actualEulerDisplacementMoment_allocated parameters radius positive
    (actualGaugeMatrixJets parameters L compact state 0) smooth
    (actualGaugeEulerKernel parameters L compact state radius)
    (fun raw shift input => actualGaugeEulerKernel_entry parameters L compact state radius raw shift input)
    rank moment inputs
  refine ⟨allocated.1, allocated.2.trans ?_⟩
  unfold actualGaugeConjugatedEulerConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index member
  have indexLe : index ≤ rank := by have := Finset.mem_range.mp member; omega
  have combined : moment+index+(rank-index)+5 = moment+rank+5 := by omega
  have bound := actualGaugeEulerKernel_moment_bound parameters L compact (rank-index) (moment+index) state radius
  rw [combined] at bound
  exact (mul_le_mul_of_nonneg_left bound
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters index)))).trans_eq
      (mul_assoc _ _ _).symm

end Grad.OriginalCartesianTameEstimate
