import GSP2PhysicalGaugeMatrix

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.SourceCollarAngular

def polarVector (component : Fin 3) (angle : ℝ) : Fin 3 → ℂ :=
  if component = 0 then physicalRadialVector angle
  else if component = 1 then physicalTangentialVector angle else physicalToroidalVector

def polarMatrixEntry (row column : Fin 3) (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  matrixPairing (polarVector row angle) matrix (polarVector column angle)

def polarEntryFrequency (row column : Fin 3) (slot : Fin 2 × Fin 2) : ℤ :=
  (if row = 2 then 0 else polarLaurentSign slot.1) +
    if column = 2 then 0 else polarLaurentSign slot.2

theorem polarMatrixEntry_laurent (row column : Fin 3) (angle : ℝ)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) :
    polarMatrixEntry row column angle matrix =
      ∑ slot : Fin 2 × Fin 2, cellExponential (polarEntryFrequency row column slot) angle *
        matrixPairing (fun index => kappaLaurentRight row slot.1 index) matrix
          (fun index => kappaLaurentRight column slot.2 index) := by
  rw [Fintype.sum_prod_type]
  fin_cases row <;> fin_cases column <;>
    simp only [polarEntryFrequency, cellExponential_add, kappaLaurentRight] <;>
    simp [Fin.sum_univ_two, polarMatrixEntry, polarVector, matrixPairing, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, polarLaurentSign, tangentialLaurentVector, radialLaurentVector,
      physicalRadialVector, physicalTangentialVector, physicalToroidalVector,
      cellExponential_one, cellExponential_neg_one, cellExponential_zero]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

def mappedMatrixFamily (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (row : Fin 3) (slot : Fin 2) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 1 :=
  composeFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 (scalarRowMapping (fun index => kappaLaurentRight row slot index))) family

theorem mappedMatrixFamily_coherent (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (coherent : FamilyCoherent family) (row : Fin 3) (slot : Fin 2) :
    FamilyCoherent (mappedMatrixFamily parameters family row slot) :=
  (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 _).comp (unitDiskAdmissible parameters) coherent

def mappedMatrixConstant (row : Fin 3) (slot : Fin 2) (grade : ℕ) : ℝ :=
  gradeProductConstant grade * fixedFamilyConstant (scalarRowMapping (fun index => kappaLaurentRight row slot index)) grade

theorem mappedMatrixConstant_nonnegative (row : Fin 3) (slot : Fin 2) (grade : ℕ) :
    0 ≤ mappedMatrixConstant row slot grade :=
  mul_nonneg (gradeProductConstant_nonnegative grade) (fixedFamilyConstant_nonnegative _ grade)

theorem mappedMatrixFamily_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (row : Fin 3) (slot : Fin 2) (grade : ℕ) :
    ‖mappedMatrixFamily parameters family row slot grade‖ ≤
      mappedMatrixConstant row slot grade * ‖family grade‖ := by
  apply (coefficientComposition_norm_le (unitDiskAdmissible parameters) grade _ _).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (constantFamily_norm_le (unitDiskAdmissible parameters) _ grade) (gradeProductConstant_nonnegative grade)) (norm_nonneg _)

theorem mappedMatrixFamily_physicalValue (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (coherent : FamilyCoherent family) (row : Fin 3) (slot : Fin 2)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (mappedMatrixFamily parameters family row slot grade) angle point =
      (scalarRowMapping (fun index => kappaLaurentRight row slot index)).comp
        (coefficientPhysicalValue (family grade) angle point) := by
  rw [mappedMatrixFamily, composeFamily, family_physicalValue_comp (unitDiskAdmissible parameters) _ _
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 _) coherent,
    constantFamily_physicalValue (unitDiskAdmissible parameters)]

end Grad.ActualGaugeSigmaPrimitives
