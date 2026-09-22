import AKAR4LiteralLambdaCircleCoordinates
import AKV21WeightedAngularHilbertContractions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients Grad.ActualPhysicalField Grad.AnnularGeneralSourceRegularity
open Grad.GaugeCoefficients.Physical.Ledger

theorem originalAngularShift_norm (parameters : PhaseParameters) (dimension : ℕ) (shift : ℤ) :
    ‖weightedAngularHilbertShift parameters dimension 0 shift‖ ≤ 1 := by
  unfold weightedAngularHilbertShift
  exact coefficientOperator_norm_le parameters 0
    (Grad.SourceCollarAngular.angularModeTranslation shift) _ _ _

theorem originalCosine_norm (parameters : PhaseParameters) (dimension : ℕ) :
    ‖weightedHilbertCosine parameters dimension 0‖ ≤ 1 := by
  unfold weightedHilbertCosine
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  have add := (norm_add_le _ _).trans (add_le_add (originalAngularShift_norm parameters dimension 1)
    (originalAngularShift_norm parameters dimension (-1)))
  norm_num [norm_inv] at *
  nlinarith only [add]

theorem originalSine_norm (parameters : PhaseParameters) (dimension : ℕ) :
    ‖weightedHilbertSine parameters dimension 0‖ ≤ 1 := by
  unfold weightedHilbertSine
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  have sub := (norm_sub_le _ _).trans (add_le_add (originalAngularShift_norm parameters dimension 1)
    (originalAngularShift_norm parameters dimension (-1)))
  norm_num only [norm_inv,norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one] at *
  nlinarith only [sub]

def originalCircleMatrix {input output : ℕ} (parameters : PhaseParameters)
    (matrix : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) : CellL2 input →L[ℂ] CellL2 output :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrix) (norm_nonneg _) (fun _ => le_rfl)

theorem originalCircleMatrix_norm {input output : ℕ} (parameters : PhaseParameters)
    (matrix : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    ‖originalCircleMatrix parameters matrix‖ ≤ ‖matrix‖ := coefficientOperator_norm_le _ _ _ _ _ _

def originalCircleRadialRow (parameters : PhaseParameters) : CellL2 3 →L[ℂ] CellL2 1 :=
  (originalCircleMatrix parameters (matrixUnit 0 0)).comp (weightedHilbertCosine parameters 3 0) +
    (originalCircleMatrix parameters (matrixUnit 0 1)).comp (weightedHilbertSine parameters 3 0)

def originalCircleTangentialRow (parameters : PhaseParameters) : CellL2 3 →L[ℂ] CellL2 1 :=
  (originalCircleMatrix parameters (matrixUnit 0 1)).comp (weightedHilbertCosine parameters 3 0) -
    (originalCircleMatrix parameters (matrixUnit 0 0)).comp (weightedHilbertSine parameters 3 0)

def originalCircleRadialColumn (parameters : PhaseParameters) : CellL2 1 →L[ℂ] CellL2 3 :=
  (originalCircleMatrix parameters (matrixUnit 0 0)).comp (weightedHilbertCosine parameters 1 0) +
    (originalCircleMatrix parameters (matrixUnit 1 0)).comp (weightedHilbertSine parameters 1 0)

def originalCircleTangentialColumn (parameters : PhaseParameters) : CellL2 1 →L[ℂ] CellL2 3 :=
  (originalCircleMatrix parameters (matrixUnit 1 0)).comp (weightedHilbertCosine parameters 1 0) -
    (originalCircleMatrix parameters (matrixUnit 0 0)).comp (weightedHilbertSine parameters 1 0)

theorem originalCircleMatrix_cosine_norm {input output : ℕ} (parameters : PhaseParameters)
    (row : Fin output) (column : Fin input) :
    ‖(originalCircleMatrix parameters (matrixUnit row column)).comp (weightedHilbertCosine parameters input 0)‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul ((originalCircleMatrix_norm parameters _).trans (matrixUnit_norm_le _ _))
      (originalCosine_norm parameters input) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))

theorem originalCircleMatrix_sine_norm {input output : ℕ} (parameters : PhaseParameters)
    (row : Fin output) (column : Fin input) :
    ‖(originalCircleMatrix parameters (matrixUnit row column)).comp (weightedHilbertSine parameters input 0)‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul ((originalCircleMatrix_norm parameters _).trans (matrixUnit_norm_le _ _))
      (originalSine_norm parameters input) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))

theorem originalCircleRadialRow_norm (parameters : PhaseParameters) : ‖originalCircleRadialRow parameters‖ ≤ 2 :=
  (norm_add_le _ _).trans ((add_le_add (originalCircleMatrix_cosine_norm parameters _ _) (originalCircleMatrix_sine_norm parameters _ _)).trans_eq (by norm_num))
theorem originalCircleTangentialRow_norm (parameters : PhaseParameters) : ‖originalCircleTangentialRow parameters‖ ≤ 2 :=
  (norm_sub_le _ _).trans ((add_le_add (originalCircleMatrix_cosine_norm parameters _ _) (originalCircleMatrix_sine_norm parameters _ _)).trans_eq (by norm_num))
theorem originalCircleRadialColumn_norm (parameters : PhaseParameters) : ‖originalCircleRadialColumn parameters‖ ≤ 2 :=
  (norm_add_le _ _).trans ((add_le_add (originalCircleMatrix_cosine_norm parameters _ _) (originalCircleMatrix_sine_norm parameters _ _)).trans_eq (by norm_num))
theorem originalCircleTangentialColumn_norm (parameters : PhaseParameters) : ‖originalCircleTangentialColumn parameters‖ ≤ 2 :=
  (norm_sub_le _ _).trans ((add_le_add (originalCircleMatrix_cosine_norm parameters _ _) (originalCircleMatrix_sine_norm parameters _ _)).trans_eq (by norm_num))

end Grad.OriginalKernelRetainedDecay
