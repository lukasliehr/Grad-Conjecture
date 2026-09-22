import AXF19SpinNorm

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

open MeasureTheory
open scoped BigOperators

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.COR12Extension
open Grad.NonlinearProduct

def componentValue (dimension : ℕ) (index : Fin dimension) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean 1 :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) index).smulRight
    (EuclideanSpace.single 0 1)

@[simp] theorem componentValue_apply {dimension : ℕ} (index : Fin dimension)
    (value : ComplexEuclidean dimension) :
    componentValue dimension index value 0 = value index := by
  simp [componentValue]

theorem vector_norm_sq_components {dimension : ℕ} (value : ComplexEuclidean dimension) :
    ‖value‖ ^ 2 = ∑ index : Fin dimension, ‖componentValue dimension index value‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro index _
  rw [PiLp.norm_sq_eq_of_L2]
  simp

theorem closedValue_norm_sq_components {dimension : ℕ}
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 field‖ ^ 2 =
      ∑ index : Fin dimension,
        ‖closedContinuousToDiskL2 (valueMapClosed (componentValue dimension index) field)‖ ^ 2 := by
  simp only [closedContinuousToDiskL2_norm_sq]
  have integrable (index : Fin dimension) : Integrable
      (fun point => ‖closedDiskLift
        (valueMapClosed (componentValue dimension index) field) point‖ ^ 2)
      (volume.restrict openUnitDisk) :=
    (memLp_two_iff_integrable_sq_norm (closedContinuous_memLp _).1).mp
      (closedContinuous_memLp _)
  rw [← integral_finsetSum _ (fun index _ => integrable index)]
  apply integral_congr_ae
  filter_upwards with point
  simp only [closedDiskLift_valueMapClosed, Function.comp_apply]
  exact vector_norm_sq_components _

def componentCore {parameters : PhaseParameters} (dimension : ℕ) (index : Fin dimension) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters 1 :=
  Grad.Constraints.valueMapCore (componentValue dimension index) parameters

theorem componentCore_derivative {parameters : PhaseParameters} {dimension : ℕ}
    (index : Fin dimension) (field : ACore parameters dimension) (cell : ℤ)
    (derivative : CartesianMultiIndex) :
    closedMultiDerivative (phaseWeightedJet parameters cell
      ((componentCore dimension index field).val cell)) derivative =
    valueMapClosed (componentValue dimension index)
      (closedMultiDerivative (phaseWeightedJet parameters cell (field.val cell)) derivative) := by
  change closedMultiDerivative (phaseWeightedJet parameters cell
    (valueMapJet (componentValue dimension index) (field.val cell))) derivative = _
  rw [← valueMapJet_phaseWeighted]
  exact valueMapJet_derivative _ _ _

theorem originalCoordinateEnergy_components {parameters : PhaseParameters}
    {dimension grade : ℕ} (field : ACore parameters dimension) (derivative : GradeMultiIndex grade) :
    originalCoordinateEnergy parameters field derivative =
      ∑ index : Fin dimension,
        originalCoordinateEnergy parameters (componentCore dimension index field) derivative := by
  unfold originalCoordinateEnergy
  rw [← Summable.tsum_finsetSum (fun index _ =>
    originalCoordinateEnergy_summable parameters (componentCore dimension index field) derivative)]
  apply tsum_congr
  intro cell
  simp only [closedDerivativeL2, LinearMap.coe_mk, AddHom.coe_mk,
    componentCore_derivative, ← Finset.mul_sum]
  rw [closedValue_norm_sq_components]

/-- The actual vector grade is the sum of its actual scalar-component energies;
no replacement norm or equivalent renorming is introduced. -/
theorem originalGradeNorm_components {parameters : PhaseParameters}
    {dimension : ℕ} (grade : ℕ) (field : ACore parameters dimension) :
    originalGradeNorm grade field ^ 2 =
      ∑ index : Fin dimension,
        originalGradeNorm grade (componentCore dimension index field) ^ 2 := by
  unfold originalGradeNorm
  simp only [originalGrade_norm_sq_eq_sum_coordinateEnergy]
  calc
    _ = ∑ derivative : GradeMultiIndex grade, ∑ index : Fin dimension,
        originalCoordinateEnergy parameters (componentCore dimension index field) derivative := by
      apply Finset.sum_congr rfl
      intro derivative _
      exact originalCoordinateEnergy_components field derivative
    _ = _ := Finset.sum_comm

end Grad.FlatSourceProjection
