import AKU22ActualAxisLiftMatrixFidelity
import AKU20ActualPlanarSourceAxisData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger

/-- Axial covector ordering (u1,u2,c); physical rows remain (U1,UT,U2). -/
def axisCovectorValue (planar : ComplexEuclidean 2) (toroidal : ℂ) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![planar 0,planar 1,toroidal]

theorem threeColumnOperator_apply {output : ℕ} (mapping : OperatorValue 3 output)
    (value : ComplexEuclidean 3) (row : Fin output) :
    mapping value row = operatorMatrix mapping row 0 * value 0 +
      operatorMatrix mapping row 1 * value 1 + operatorMatrix mapping row 2 * value 2 := by
  have expansion : value = value 0 • EuclideanSpace.single 0 1 +
      value 1 • EuclideanSpace.single 1 1 + value 2 • EuclideanSpace.single 2 1 := by
    apply PiLp.ext
    intro component
    fin_cases component <;> simp
  conv_lhs => rw [expansion,map_add,map_add,map_smul,map_smul,map_smul]
  rw [operatorMatrix_single,operatorMatrix_single,operatorMatrix_single]
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

/-- Both tilt couplings survive in the exact two projected inverse-Gram
rows; they combine into K0(u-tau*c). -/
theorem firstTwo_tiltedAxisGram_covector (gram : Matrix (Fin 2) (Fin 2) ℂ)
    (tilt planar : ComplexEuclidean 2) (toroidal : ℂ) :
    matrixOperator (firstTwoProjection * tiltedAxisGram gram tilt) (axisCovectorValue planar toroidal) =
      matrixOperator gram (planar - toroidal • tilt) := by
  apply PiLp.ext
  intro row
  rw [threeColumnOperator_apply,planarOperator_apply_entries,operatorMatrix_matrixOperator,operatorMatrix_matrixOperator]
  fin_cases row <;> simp [firstTwoProjection,tiltedAxisGram,axisCovectorValue,Matrix.mul_apply,Fin.sum_univ_three] <;> ring

/-- The literal original F^-T reconstructs the physical U, including its
actual toroidal component, from the same covector pair. -/
theorem tiltedAxisInverse_transpose_covector (inverse : Matrix (Fin 2) (Fin 2) ℂ)
    (tilt planar : ComplexEuclidean 2) (toroidal : ℂ) :
    matrixOperator (tiltedAxisInverse inverse tilt).transpose (axisCovectorValue planar toroidal) =
      WithLp.toLp 2 ![matrixOperator inverse.transpose (planar-toroidal • tilt) 0,
        toroidal,matrixOperator inverse.transpose (planar-toroidal • tilt) 1] := by
  apply PiLp.ext
  intro row
  rw [threeColumnOperator_apply,operatorMatrix_matrixOperator]
  fin_cases row <;> simp [tiltedAxisInverse,axisCovectorValue,
    planarOperator_apply_entries,operatorMatrix_matrixOperator] <;> ring

def axisPhysicalEvaluation {parameters : PhaseParameters} (dimension : ℕ) (angle : ℝ) :
    Grad.AxisCore.AxisSmoothCore parameters dimension →ₗ[ℂ] ComplexEuclidean dimension where
  toFun data := axisPhysicalValue data angle
  map_add' first second := by
    have total := (axisPhysicalValue_hasSum first angle).add (axisPhysicalValue_hasSum second angle)
    apply (axisPhysicalValue_hasSum (first+second) angle).unique
    apply total.congr_fun
    intro cell
    exact smul_add _ _ _
  map_smul' scalar data := by
    have total := (scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)).hasSum (axisPhysicalValue_hasSum data angle)
    apply (axisPhysicalValue_hasSum (scalar • data) angle).unique
    apply total.congr_fun
    intro cell
    exact smul_comm (fourierPhase cell angle) scalar (data.val cell)

end Grad.FinitePhysicalJetLift
