import ACP6ForceCellCalculus
import SCC19CellFourierRealization

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1400000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.SourceCollarCoefficients Grad.SourceCollarAngular Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

def originalForceMatrix (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (axialAngle : ℝ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  (rotatedPhysicalFrameMatrix parameters 1 1 epsilon field axialAngle point *
    Matrix.diagonal ![1, 1, (L : ℂ)⁻¹]).transpose *
      (originalPhysicalFrameMatrix parameters L epsilon field axialAngle point)⁻¹.transpose

theorem forceMatrixFamily_actual (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (forceMatrixFamily parameters L epsilon field) grade angle point =
      originalForceMatrix parameters L epsilon field angle point := by
  rw [forceMatrixFamily_matrix parameters L rho epsilon field low,
    originalRotatedFamily_matrix]
  rfl

theorem forcePolarCellTerm_fourier (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2)
    (radius polarAngle axialAngle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle *
      forcePolarCellTerm parameters L rho epsilon field kind low component slot cell (radius, polarAngle) 0)
      (cellExponential (forceLaurentFrequency kind component slot) polarAngle *
        matrixPairing (forceLaurentLeft kind slot.1)
          (originalForceMatrix parameters L epsilon field axialAngle
            (polarClosedPoint radius polarAngle nonnegative bounded))
          (fun index => kappaLaurentRight component slot.2 index)) := by
  have sum := (coefficientColumnJet_scalarFourier parameters
    (mappedForceFamily parameters L epsilon field (scalarRowMapping (forceLaurentLeft kind slot.1)))
    (mappedForceFamily_coherent parameters L rho epsilon field _ low)
    (kappaLaurentRight component slot.2) radius polarAngle axialAngle nonnegative bounded).mul_left
      (cellExponential (forceLaurentFrequency kind component slot) polarAngle)
  rw [mappedForceFamily_physicalValue parameters L rho epsilon field _ low,
    ContinuousLinearMap.comp_apply, scalarRowMapping_pairing] at sum
  change HasSum _ (cellExponential (forceLaurentFrequency kind component slot) polarAngle *
    matrixPairing (forceLaurentLeft kind slot.1)
      (familyMatrix (forceMatrixFamily parameters L epsilon field) 0 axialAngle
        (polarClosedPoint radius polarAngle nonnegative bounded))
      (fun index => kappaLaurentRight component slot.2 index)) at sum
  rw [forceMatrixFamily_actual parameters L rho epsilon field low] at sum
  apply sum.congr_fun
  intro cell
  change fourierPhase cell axialAngle *
    (cellExponential (forceLaurentFrequency kind component slot) polarAngle * _) = _
  exact mul_left_comm _ _ _

theorem forcePolarCell_actual_fourier (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius polarAngle axialAngle : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle *
      forcePolarCell parameters L rho epsilon field kind low component cell (radius, polarAngle) 0)
      (forcePolarComponent kind polarAngle
        (originalForceMatrix parameters L epsilon field axialAngle
          (polarClosedPoint radius polarAngle nonnegative bounded)) component) := by
  have sum := hasSum_sum (s := Finset.univ) (fun slot _ =>
    forcePolarCellTerm_fourier parameters L rho epsilon field kind low component slot
      radius polarAngle axialAngle nonnegative bounded)
  rw [← forcePolarComponent_laurent] at sum
  apply sum.congr_fun
  intro cell
  change fourierPhase cell axialAngle *
    (PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : PhysicalValue 1 →L[ℂ] ℂ)
      ((∑ slot, forcePolarCellTerm parameters L rho epsilon field kind low component slot cell) (radius, polarAngle)) = _
  rw [Finset.sum_apply, map_sum, Finset.mul_sum]
  rfl

end Grad.ActualCurrentPrimitives
