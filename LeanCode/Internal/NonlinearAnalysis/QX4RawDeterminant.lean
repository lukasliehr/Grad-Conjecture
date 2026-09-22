import QX3DeterminantAlgebra

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.RawForward

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.QuotientProjection Grad.AxisSplit

variable {parameters : PhaseParameters}

theorem determinantOperation_coordinate_first (first second third : ACore parameters 3)
    (coordinate : Fin 2) :
    determinantOperation parameters (coordinateCore parameters coordinate first) second third =
      coordinateCore parameters coordinate (determinantOperation parameters first second third) := by
  change actualMultilinearProduct parameters determinantMultilinear
    ![coordinateCore parameters coordinate first, second, third] =
    coordinateCore parameters coordinate
      (actualMultilinearProduct parameters determinantMultilinear ![first, second, third])
  have tuple : Function.update ![first, second, third] (0 : Fin 3)
      (coordinateCore parameters coordinate first) =
      ![coordinateCore parameters coordinate first, second, third] := by
    funext index
    fin_cases index <;> rfl
  rw [← tuple]
  exact actualProduct_coordinate determinantMultilinear ![first, second, third] 0 coordinate

theorem determinantOperation_coordinate_second (first second third : ACore parameters 3)
    (coordinate : Fin 2) :
    determinantOperation parameters first (coordinateCore parameters coordinate second) third =
      coordinateCore parameters coordinate (determinantOperation parameters first second third) := by
  change actualMultilinearProduct parameters determinantMultilinear
    ![first, coordinateCore parameters coordinate second, third] =
    coordinateCore parameters coordinate
      (actualMultilinearProduct parameters determinantMultilinear ![first, second, third])
  have tuple : Function.update ![first, second, third] (1 : Fin 3)
      (coordinateCore parameters coordinate second) =
      ![first, coordinateCore parameters coordinate second, third] := by
    funext index
    fin_cases index <;> rfl
  rw [← tuple]
  exact actualProduct_coordinate determinantMultilinear ![first, second, third] 1 coordinate

theorem radiusSquaredCore_coordinates {dimension : ℕ} (field : ACore parameters dimension) :
    radiusSquaredCore parameters field =
      coordinateCore parameters 0 (coordinateCore parameters 0 field) +
      coordinateCore parameters 1 (coordinateCore parameters 1 field) := by
  apply acore_ext
  intro cell point
  rw [radiusSquaredCore_value, acore_add_value]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [coordinateCore_val, coordinateJet_value, smul_smul,
    Fin.sum_univ_two, pow_two, add_smul]

/-- Exact determinant reconstruction, including the axis. Only spatial
multiplication occurs; the alternating convolution product supplies cancellation. -/
theorem determinantOperation_euler_rotation (field third : ACore parameters 3) :
    determinantOperation parameters (eulerCore parameters field) (rotationCore parameters field) third =
      radiusSquaredCore parameters (determinantOperation parameters
        (partialCore parameters 0 field) (partialCore parameters 1 field) third) := by
  change determinantOperation parameters
      (coordinateCore parameters 0 (partialCore parameters 0 field) +
        coordinateCore parameters 1 (partialCore parameters 1 field))
      (coordinateCore parameters 0 (partialCore parameters 1 field) -
        coordinateCore parameters 1 (partialCore parameters 0 field)) third = _
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    determinantOperation_coordinate_first, determinantOperation_coordinate_second]
  rw [determinantOperation_self, determinantOperation_self,
    determinantOperation_swap (partialCore parameters 0 field) (partialCore parameters 1 field) third]
  simp only [map_zero, map_neg, add_zero, zero_add, sub_neg_eq_add]
  exact (radiusSquaredCore_coordinates _).symm

theorem radiusSquaredCore_removeAngular {dimension : ℕ} (field : ACore parameters dimension) :
    radiusSquaredCore parameters (removeAngularCore parameters field) =
      removeAngularCore parameters (radiusSquaredCore parameters field) := by
  change radiusSquaredCore parameters (field - angularCore parameters 0 field) =
    radiusSquaredCore parameters field - angularCore parameters 0 (radiusSquaredCore parameters field)
  rw [map_sub, angularCore_radiusSquaredCore]

theorem rawReconstruction_fourth (cellLength : ℝ) (state : QuotientState parameters) :
    rawReconstructionCore parameters (quotientPolynomialRows parameters cellLength state) 3 =
      originalRawRowsCore parameters cellLength state 3 := by
  change radiusSquaredCore parameters
      (removeAngularCore parameters (determinantOperation parameters
        (partialCore parameters 0 (stateField state))
        (partialCore parameters 1 (stateField state)) (affineStateCore parameters cellLength state))) =
    removeAngularCore parameters (determinantOperation parameters (eulerCore parameters (stateField state))
      (rotationCore parameters (stateField state)) (affineStateCore parameters cellLength state))
  have determinant := determinantOperation_euler_rotation
    (stateField state) (affineStateCore parameters cellLength state)
  calc
    _ = removeAngularCore parameters (radiusSquaredCore parameters
        (determinantOperation parameters (partialCore parameters 0 (stateField state))
          (partialCore parameters 1 (stateField state)) (affineStateCore parameters cellLength state))) :=
      radiusSquaredCore_removeAngular _
    _ = _ := congrArg (removeAngularCore parameters) determinant.symm

end Grad.RawForward
