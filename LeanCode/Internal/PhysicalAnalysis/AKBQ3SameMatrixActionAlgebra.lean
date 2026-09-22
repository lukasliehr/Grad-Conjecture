import AKBQ2SameScaledGaugeMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualSmoothPhysicalField Grad.ActualGaugeSigmaPrimitives
open Grad.Constraints Grad.Constraints.Gauges Grad.CartesianStartup

 theorem operatorMatrix_action {input output : ℕ} (mapping : OperatorValue input output)
    (value : PhysicalValue input) :
    mapping value = WithLp.toLp 2 ((operatorMatrix mapping).mulVec value) := by
  apply PiLp.ext
  intro row
  have expanded := congrArg (fun current : PhysicalValue input => mapping current row) (operatorBasis_expansion value)
  rw [map_sum] at expanded
  change (PiLp.proj 2 (fun _ : Fin output => ℂ) row : PhysicalValue output →L[ℂ] ℂ)
    (∑ column : Fin input, mapping (value column • operatorBasis column)) = _ at expanded
  rw [map_sum] at expanded
  rw [← expanded]
  simp only [map_smul,smul_eq_mul,Matrix.mulVec,dotProduct,operatorMatrix,operatorBasis]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- The two literal polar gauge rows of any Cartesian matrix action. -/
 theorem polarGauge_action (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    polarTangentialComponent angle (planarPartMap (WithLp.toLp 2 (matrix.mulVec (cartesianCovariantValue angle value)))) =
      ∑ component : Fin 3, polarMatrixEntry 1 component angle matrix * value component := by
  rw [cartesianCovariantValue_apply]
  simp [polarTangentialComponent,planarPartMap,polarMatrixEntry,polarVector,matrixPairing,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three,physicalRadialVector,physicalTangentialVector,physicalToroidalVector]
  ring

 theorem toroidalGauge_action (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    toroidalPartMap (WithLp.toLp 2 (matrix.mulVec (cartesianCovariantValue angle value))) 0 =
      ∑ component : Fin 3, polarMatrixEntry 2 component angle matrix * value component := by
  rw [cartesianCovariantValue_apply]
  simp [toroidalPartMap,polarMatrixEntry,polarVector,matrixPairing,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three,physicalRadialVector,physicalTangentialVector,physicalToroidalVector]
  ring

end Grad.ActualScaledNativeCoefficients
