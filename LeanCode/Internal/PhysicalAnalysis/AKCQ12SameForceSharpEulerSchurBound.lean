import AKCQ11SharpEulerDisplacementMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularVariational Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.Allocation

def actualForceConjugatedEulerConstant (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (rank moment : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (rank+1), (rank.choose index : ℝ) * positiveEulerRatioConstant parameters index *
    actualForceEulerMomentConstant parameters L kind (moment+index) (rank-index)

theorem actualForceConjugatedEulerConstant_nonnegative (parameters : PhaseParameters) (L : ℝ)
    (kind : Fin 2) (rank moment : ℕ) :
    0 ≤ actualForceConjugatedEulerConstant parameters L kind rank moment :=
  Finset.sum_nonneg (fun index _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters index)))
    (actualForceEulerMomentConstant_nonnegative parameters L kind (moment+index) (rank-index)))

/-- SAME actual force matrices, full original phase and every full cell.
Raw derivative rank and phase displacement rank are allocated jointly,
leaving exactly one physical budget at moment+rank+6. -/
theorem actualForceConjugatedEuler_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (kind : Fin 2) (rank moment : ℕ) (state : RadialCoefficientState parameters L compact)
    (radius : RadialPoint) (positive : 0 < radius.val) (inputs : (ℤ × ℤ) → (ℤ × ℤ)) :
    Summable (fun (shift : ℤ × ℤ) => Grad.AnnularVariational.annularFrequency shift.1 shift.2 ^ moment *
      ‖actualConjugatedEulerEntry parameters (actualForceMatrixJets parameters L compact state kind 0)
        rank radius.val shift (inputs shift)‖) ∧
    actualEulerDisplacementMoment parameters (actualForceMatrixJets parameters L compact state kind 0)
      rank moment radius.val inputs ≤
        actualForceConjugatedEulerConstant parameters L kind rank moment *
          physicalBudget parameters state.data.field state.data.rho state.data.epsilon (moment+rank+6) := by
  have smooth (shift input : ℤ × ℤ) :
      ContDiff ℝ ∞ (fun point => actualForceMatrixJets parameters L compact state kind 0 point shift input) :=
    derivativeTower_smooth (fun raw point => actualForceMatrixJets parameters L compact state kind raw point shift input)
      (fun raw point => actualForceMatrixJets_derivative parameters L compact state kind raw point shift input) 0
  have allocated := actualEulerDisplacementMoment_allocated parameters radius positive
    (actualForceMatrixJets parameters L compact state kind 0) smooth
    (actualForceEulerKernel parameters L compact state kind radius)
    (fun raw shift input => actualForceEulerKernel_entry parameters L compact state kind radius raw shift input)
    rank moment inputs
  refine ⟨allocated.1, allocated.2.trans ?_⟩
  unfold actualForceConjugatedEulerConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index member
  have indexLe : index ≤ rank := by have := Finset.mem_range.mp member; omega
  have combined : moment+index+(rank-index)+6 = moment+rank+6 := by omega
  have bound := actualForceEulerKernel_moment_bound parameters L compact kind (rank-index) (moment+index) state radius
  rw [combined] at bound
  exact (mul_le_mul_of_nonneg_left bound
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters index)))).trans_eq
      (mul_assoc _ _ _).symm

end Grad.OriginalCartesianTameEstimate
