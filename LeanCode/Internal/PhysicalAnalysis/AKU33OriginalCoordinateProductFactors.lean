import AKU32ExactCoordinateAxisCalculus
import AKU31LiteralCartesianForwardForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange

/-- An exact coordinate factor in any slot of the original all-cell
multilinear product. The Fourier convolution is preserved literally. -/
theorem originalProduct_coordinate_slot {parameters : PhaseParameters} {arity outputDimension : ℕ}
    {dimensions : Fin (arity+1) → ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity+1)) → ACore parameters (dimensions index))
    (slot : Fin (arity+1)) (coordinate : Fin 2) :
    actualMultilinearProduct parameters multiplication
      (Function.update fields slot (coordinateCore parameters coordinate (fields slot))) =
      coordinateCore parameters coordinate (actualMultilinearProduct parameters multiplication fields) := by
  apply acore_ext
  intro cell point
  rw [actualMultilinearProduct_isActual,coordinateCore_val,coordinateJet_value,
    actualMultilinearProduct_isActual]
  unfold productCoefficientValue
  rw [← tsum_const_smul'' (point.val coordinate)]
  apply tsum_congr
  intro cells
  have tuple : (fun index => ((Function.update fields slot
      (coordinateCore parameters coordinate (fields slot)) index).val (cells.val index)).value point) =
      Function.update (fun index => ((fields index).val (cells.val index)).value point)
        slot ((point.val coordinate : ℂ) • ((fields slot).val (cells.val slot)).value point) := by
    funext index
    by_cases same : index = slot
    · subst index
      simp only [Function.update_self,coordinateCore_val,coordinateJet_value,Complex.coe_smul]
    · rw [Function.update_of_ne same,Function.update_of_ne same]
  rw [tuple,multiplication.map_update_smul,Function.update_eq_self,Complex.coe_smul]

theorem determinant_coordinate_first {parameters : PhaseParameters}
    (coordinate : Fin 2) (first second third : ACore parameters 3) :
    determinantOperation parameters (coordinateCore parameters coordinate first) second third =
      coordinateCore parameters coordinate (determinantOperation parameters first second third) := by
  change actualMultilinearProduct parameters determinantMultilinear
    ![coordinateCore parameters coordinate first,second,third] = _
  have tuple : ![coordinateCore parameters coordinate first,second,third] =
      Function.update ![first,second,third] 0 (coordinateCore parameters coordinate first) := by
    funext index
    fin_cases index <;> rfl
  rw [tuple]
  exact originalProduct_coordinate_slot (parameters := parameters) determinantMultilinear
    ![first,second,third] 0 coordinate

theorem determinant_coordinate_second {parameters : PhaseParameters}
    (coordinate : Fin 2) (first second third : ACore parameters 3) :
    determinantOperation parameters first (coordinateCore parameters coordinate second) third =
      coordinateCore parameters coordinate (determinantOperation parameters first second third) := by
  change actualMultilinearProduct parameters determinantMultilinear
    ![first,coordinateCore parameters coordinate second,third] = _
  have tuple : ![first,coordinateCore parameters coordinate second,third] =
      Function.update ![first,second,third] 1 (coordinateCore parameters coordinate second) := by
    funext index
    fin_cases index <;> rfl
  rw [tuple]
  exact originalProduct_coordinate_slot (parameters := parameters) determinantMultilinear
    ![first,second,third] 1 coordinate

theorem determinant_coordinate_third {parameters : PhaseParameters}
    (coordinate : Fin 2) (first second third : ACore parameters 3) :
    determinantOperation parameters first second (coordinateCore parameters coordinate third) =
      coordinateCore parameters coordinate (determinantOperation parameters first second third) := by
  change actualMultilinearProduct parameters determinantMultilinear
    ![first,second,coordinateCore parameters coordinate third] = _
  have tuple : ![first,second,coordinateCore parameters coordinate third] =
      Function.update ![first,second,third] 2 (coordinateCore parameters coordinate third) := by
    funext index
    fin_cases index <;> rfl
  rw [tuple]
  exact originalProduct_coordinate_slot (parameters := parameters) determinantMultilinear
    ![first,second,third] 2 coordinate

end Grad.FinitePhysicalJetLift
