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
def actualSigmaMatrixJets (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) :
    ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 1 :=
  rowMultiplicationEntry 3 (fun component => sigmaScalar parameters L state.data.rho state.data.epsilon
    state.data.field state.low component rank radius) shift input

theorem actualSigmaMatrixJets_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (rank : ℕ) (radius : ℝ) (shift input : ℤ × ℤ) :
    HasDerivAt (fun point => actualSigmaMatrixJets parameters L compact state rank point shift input)
      (actualSigmaMatrixJets parameters L compact state (rank+1) radius shift input) radius :=
  rowMultiplicationEntry_hasDerivAt 3 _ _
    (fun component point mode => sigmaScalar_hasDerivAt parameters L state.data.rho state.data.epsilon
      state.data.field state.low component rank point mode) radius shift input

def actualSigmaEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) : ℕ → RadialKernel parameters radius 3 1
  | 0 => radialSigmaKernel parameters L compact state radius 0
  | rank+1 => rawEulerKernel radius (fun raw => radialSigmaKernel parameters L compact state radius raw)
      (positiveEulerTerms rank)

def actualSigmaRawMomentConstant (parameters : PhaseParameters) (L : ℝ)
    (moment raw : ℕ) : ℝ :=
  Real.exp (parameters.sigma0+2*parameters.gamma) * (∑ component : Fin 3, sigmaScalarConstant parameters L component moment raw)

def actualSigmaEulerMomentConstant (parameters : PhaseParameters) (L : ℝ)
    (moment : ℕ) : ℕ → ℝ
  | 0 => actualSigmaRawMomentConstant parameters L moment 0
  | rank+1 => rawEulerMomentConstant (actualSigmaRawMomentConstant parameters L moment) (positiveEulerTerms rank)

theorem actualSigmaRawMomentConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (moment raw : ℕ) :
    0 ≤ actualSigmaRawMomentConstant parameters L moment raw :=
  mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun component _ => sigmaScalarConstant_nonnegative parameters L component moment raw))

theorem actualSigmaEulerMomentConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (moment rank : ℕ) :
    0 ≤ actualSigmaEulerMomentConstant parameters L moment rank := by
  cases rank with
  | zero => exact actualSigmaRawMomentConstant_nonnegative parameters L moment 0
  | succ rank =>
      exact rawEulerMomentConstant_nonnegative _
        (actualSigmaRawMomentConstant_nonnegative parameters L moment) _

/-- The kernel is the actual Euler derivative of the original sigma matrix,
including the axis and every input cell. -/
theorem actualSigmaEulerKernel_entry (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) (rank : ℕ) (shift input : ℤ × ℤ) :
    (actualSigmaEulerKernel parameters L compact state radius rank).entry shift input =
      vectorEulerIteratedDerivative rank
        (fun point => actualSigmaMatrixJets parameters L compact state 0 point shift input) radius.val := by
  cases rank with
  | zero => rfl
  | succ rank =>
      exact rawEulerKernel_actual radius _
        (fun raw point => actualSigmaMatrixJets parameters L compact state raw point shift input)
        (fun raw point => actualSigmaMatrixJets_derivative parameters L compact state raw point shift input)
        shift input (fun _ => rfl) rank

/-- Sharp joint raw-Euler/displacement budget for the same original sigma.
The constant is independent of the state and radius; there is one high norm. -/
theorem actualSigmaEulerKernel_moment_bound (parameters : PhaseParameters) (L compact : ℝ)
    (rank moment : ℕ) (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (actualSigmaEulerKernel parameters L compact state radius rank) ≤
      actualSigmaEulerMomentConstant parameters L moment rank *
        physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+rank+5) := by
  cases rank with
  | zero => exact radialSigmaKernel_moment_le parameters L compact state radius 0 moment
  | succ rank =>
      apply rawEulerKernel_moment_bound
      intro term member
      have rawBound := radialSigmaKernel_moment_le parameters L compact state radius (term.1+1) moment
      have ordered := positiveEulerTerms_rank rank term member
      exact rawBound.trans (mul_le_mul_of_nonneg_left
        (physicalBudget_monotone parameters state.data.field state.data.rho state.data.epsilon (by omega))
        (actualSigmaRawMomentConstant_nonnegative parameters L moment (term.1+1)))



def actualSigmaConjugatedEulerConstant (parameters : PhaseParameters) (L : ℝ)
    (rank moment : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (rank+1), (rank.choose index : ℝ) * positiveEulerRatioConstant parameters index *
    actualSigmaEulerMomentConstant parameters L (moment+index) (rank-index)

theorem actualSigmaConjugatedEulerConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (rank moment : ℕ) :
    0 ≤ actualSigmaConjugatedEulerConstant parameters L rank moment :=
  Finset.sum_nonneg (fun index _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters index)))
    (actualSigmaEulerMomentConstant_nonnegative parameters L (moment+index) (rank-index)))

/-- SAME actual sigma matrices, full original phase and every full cell.
Raw derivative rank and phase displacement rank are allocated jointly,
leaving exactly one physical budget at moment+rank+5. -/
theorem actualSigmaConjugatedEuler_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (rank moment : ℕ) (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) (positive : 0 < radius.val) (inputs : (ℤ × ℤ) → (ℤ × ℤ)) :
    Summable (fun (shift : ℤ × ℤ) => Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ moment *
      ‖actualConjugatedEulerEntry parameters (actualSigmaMatrixJets parameters L compact state 0)
        rank radius.val shift (inputs shift)‖) ∧
    actualEulerDisplacementMoment parameters (actualSigmaMatrixJets parameters L compact state 0)
      rank moment radius.val inputs ≤
        actualSigmaConjugatedEulerConstant parameters L rank moment *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+rank+5) := by
  have smooth (shift input : ℤ × ℤ) :
      ContDiff ℝ ∞ (fun point => actualSigmaMatrixJets parameters L compact state 0 point shift input) :=
    derivativeTower_smooth (fun raw point => actualSigmaMatrixJets parameters L compact state raw point shift input)
      (fun raw point => actualSigmaMatrixJets_derivative parameters L compact state raw point shift input) 0
  have allocated := actualEulerDisplacementMoment_allocated parameters radius positive
    (actualSigmaMatrixJets parameters L compact state 0) smooth
    (actualSigmaEulerKernel parameters L compact state radius)
    (fun raw shift input => actualSigmaEulerKernel_entry parameters L compact state radius raw shift input)
    rank moment inputs
  refine ⟨allocated.1, allocated.2.trans ?_⟩
  unfold actualSigmaConjugatedEulerConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index member
  have indexLe : index ≤ rank := by have := Finset.mem_range.mp member; omega
  have combined : moment+index+(rank-index)+5 = moment+rank+5 := by omega
  have bound := actualSigmaEulerKernel_moment_bound parameters L compact (rank-index) (moment+index) state radius
  rw [combined] at bound
  exact (mul_le_mul_of_nonneg_left bound
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters index)))).trans_eq
      (mul_assoc _ _ _).symm

end Grad.OriginalCartesianTameEstimate
