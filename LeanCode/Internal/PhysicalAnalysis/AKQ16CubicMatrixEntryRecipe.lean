import AKQ15ActualAxisInverseGramFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger

def cubicMatrixEntryRecipe (matrix : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-(14 : ℂ) * matrix 0 1 + 2 * matrix 1 0) / 3,
      (10 * matrix 0 0 - 2 * matrix 1 1) / 3;
    (2 * matrix 0 0 - 10 * matrix 1 1) / 3,
      (-2 * matrix 0 1 + 14 * matrix 1 0) / 3]

theorem planarOperator_apply_entries (mapping : OperatorValue 2 2) (value : ComplexEuclidean 2) (row : Fin 2) :
    mapping value row = operatorMatrix mapping row 0 * value 0 + operatorMatrix mapping row 1 * value 1 := by
  have expansion : value = value 0 • EuclideanSpace.single 0 1 + value 1 • EuclideanSpace.single 1 1 := by
    apply PiLp.ext
    intro component
    fin_cases component <;> simp
  conv_lhs => rw [expansion,map_add,map_smul,map_smul]
  rw [operatorMatrix_single,operatorMatrix_single]
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

/-- Exact finite recipe for the actual div(K Ucal(r²ell)) map. No
symmetry, realness or smallness hypothesis is needed for this identity. -/
theorem cubicDeterminantOperator_matrix (mapping : OperatorValue 2 2) :
    operatorMatrix (cubicDeterminantOperator mapping) = cubicMatrixEntryRecipe (operatorMatrix mapping) := by
  ext row column
  rw [operatorMatrix_single]
  fin_cases row <;> fin_cases column <;>
    simp [cubicDeterminantOperator,cubicDeterminantLinear,
      quadraticDivergenceCoefficients,quadraticValueMap,cubicComplementVectorCoefficients,
      planarOperator_apply_entries mapping,cubicMatrixEntryRecipe] <;> ring

structure CubicEntryTerm where
  scalar : ℂ
  targetRow : Fin 2
  sourceRow : Fin 2
  sourceColumn : Fin 2
  targetColumn : Fin 2

def cubicEntryTerms : Fin 8 → CubicEntryTerm :=
  ![⟨-14/3,0,0,1,0⟩,⟨2/3,0,1,0,0⟩,
    ⟨10/3,0,0,0,1⟩,⟨-2/3,0,1,1,1⟩,
    ⟨2/3,1,0,0,0⟩,⟨-10/3,1,1,1,0⟩,
    ⟨-2/3,1,0,1,1⟩,⟨14/3,1,1,0,1⟩]

theorem cubicMatrixEntryRecipe_finite (matrix : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ term : Fin 8, (cubicEntryTerms term).scalar •
      ((Matrix.single (cubicEntryTerms term).targetRow (cubicEntryTerms term).sourceRow 1) *
        (matrix * Matrix.single (cubicEntryTerms term).sourceColumn (cubicEntryTerms term).targetColumn 1))) =
      cubicMatrixEntryRecipe matrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [cubicEntryTerms,Fin.sum_univ_succ,cubicMatrixEntryRecipe,Matrix.mul_apply,
      Matrix.single_apply] <;> ring

end Grad.FinitePhysicalJetLift
