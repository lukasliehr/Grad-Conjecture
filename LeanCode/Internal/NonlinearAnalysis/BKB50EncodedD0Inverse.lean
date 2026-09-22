import BKB49ActualMassEquation

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Ledger

theorem constantMatrixKernel_comp {input middle output : ℕ}
    (parameters : PhaseParameters)
    (outer : ComplexEuclidean middle →L[ℂ] ComplexEuclidean output)
    (inner : ComplexEuclidean input →L[ℂ] ComplexEuclidean middle) :
    fullKernelComposition
        (constantMatrixKernel parameters middle output outer)
        (constantMatrixKernel parameters input middle inner) =
      constantMatrixKernel parameters input output (outer.comp inner) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro total frequency
  rw [fullKernelComposition_entry,
    tsum_eq_single (0, 0) (by
      intro shift nonzero
      rw [constantMatrixKernel_entry parameters middle output outer,
        constantMatrixKernel_entry parameters input middle inner]
      simp only [if_neg nonzero, ContinuousLinearMap.comp_zero])]
  rw [constantMatrixKernel_entry parameters middle output outer,
    constantMatrixKernel_entry parameters input middle inner,
    constantMatrixKernel_entry parameters input output (outer.comp inner)]
  by_cases totalZero : total = (0, 0)
  · subst total
    simp only [sub_self, if_pos]
    rfl
  · have subzero : total - (0, 0) = total := sub_zero total
    simp only [subzero, if_neg totalZero, ContinuousLinearMap.zero_comp]

theorem diagonalThreeMap_inverse_right :
    (diagonalThreeMap (-2) (-1) 1).comp
        (diagonalThreeMap (-(2 : ℂ)⁻¹) (-1) 1) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 3) := by
  apply operatorMatrix_injective
  rw [operatorMatrix_comp, operatorMatrix_one]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [diagonalThreeMap, operatorMatrix_add, operatorMatrix_smul,
      operatorMatrix_matrixUnit, Matrix.mul_apply,
      Matrix.single_apply]

theorem diagonalThreeMap_inverse_left :
    (diagonalThreeMap (-(2 : ℂ)⁻¹) (-1) 1).comp
        (diagonalThreeMap (-2) (-1) 1) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 3) := by
  apply operatorMatrix_injective
  rw [operatorMatrix_comp, operatorMatrix_one]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [diagonalThreeMap, operatorMatrix_add, operatorMatrix_smul,
      operatorMatrix_matrixUnit, Matrix.mul_apply,
      Matrix.single_apply]

theorem constantMatrixKernel_id (parameters : PhaseParameters) (dimension : ℕ) :
    constantMatrixKernel parameters dimension dimension
        (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) =
      fullIdentityKernel parameters dimension := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  by_cases zero : shift = (0, 0)
  · subst shift
    rw [constantMatrixKernel_entry, fullIdentityKernel_entry_zero]
    simp only [if_pos]
  · rw [constantMatrixKernel_entry,
      fullIdentityKernel_entry_ne_zero parameters dimension shift input zero]
    simp only [if_neg zero]

theorem encodedD0Kernel_inverse_right (parameters : PhaseParameters) :
    fullKernelComposition (encodedD0Kernel parameters)
        (encodedD0InverseKernel parameters) =
      fullIdentityKernel parameters 3 := by
  unfold encodedD0Kernel encodedD0InverseKernel
  rw [constantMatrixKernel_comp, diagonalThreeMap_inverse_right]
  exact constantMatrixKernel_id parameters 3

theorem encodedD0Kernel_inverse_left (parameters : PhaseParameters) :
    fullKernelComposition (encodedD0InverseKernel parameters)
        (encodedD0Kernel parameters) =
      fullIdentityKernel parameters 3 := by
  unfold encodedD0Kernel encodedD0InverseKernel
  rw [constantMatrixKernel_comp, diagonalThreeMap_inverse_left]
  exact constantMatrixKernel_id parameters 3

end Grad.BoundaryKernelAction
