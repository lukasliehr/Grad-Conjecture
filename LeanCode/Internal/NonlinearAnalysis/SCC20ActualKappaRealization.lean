import SCC19CellFourierRealization

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarAngular

theorem physicalKappa_sub (angle : ℝ) (first second : Matrix (Fin 3) (Fin 3) ℂ) (component : Fin 3) :
    physicalKappa angle (first - second) component =
      physicalKappa angle first component - physicalKappa angle second component := by
  fin_cases component <;>
    simp [physicalKappa, matrixPairing, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      physicalRadialVector, physicalTangentialVector, physicalToroidalVector] <;> ring

theorem physicalKappa_deviation (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) (component : Fin 3) :
    physicalKappa angle (matrix + 1) component =
      physicalKappa angle matrix component - (![0, -1, 0] : Fin 3 → ℂ) component := by
  rw [← sub_neg_eq_add, physicalKappa_sub]
  have reference := congrFun (physicalKappa_reference angle) component
  rw [referenceSignedCofactor_eq] at reference
  rw [reference]

theorem kappaPolarCellTerm_fourier (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2)
    (radius polarAngle axialAngle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle *
      kappaPolarCellTerm parameters L rho epsilon field low component slot cell (radius, polarAngle) 0)
      (cellExponential (kappaLaurentFrequency component slot) polarAngle *
        matrixPairing (tangentialLaurentVector slot.1)
          (originalPhysicalSignedCofactor parameters L epsilon field axialAngle
            (polarClosedPoint radius polarAngle nonnegative bounded) + 1)
          (fun index => kappaLaurentRight component slot.2 index)) := by
  have sum := (coefficientColumnJet_scalarFourier parameters
    (mappedCofactorFamily parameters L epsilon field (scalarRowMapping (tangentialLaurentVector slot.1)))
    (mappedCofactorFamily_coherent parameters L rho epsilon field _ low)
    (kappaLaurentRight component slot.2) radius polarAngle axialAngle nonnegative bounded).mul_left
      (cellExponential (kappaLaurentFrequency component slot) polarAngle)
  rw [mappedCofactorFamily_physicalValue parameters L rho epsilon field _ low,
    ContinuousLinearMap.comp_apply, scalarRowMapping_pairing] at sum
  change HasSum _ (cellExponential (kappaLaurentFrequency component slot) polarAngle *
    matrixPairing (tangentialLaurentVector slot.1)
      (familyMatrix (originalCofactorDeviation parameters L epsilon field) 0 axialAngle
        (polarClosedPoint radius polarAngle nonnegative bounded))
      (fun index => kappaLaurentRight component slot.2 index)) at sum
  rw [originalCofactorDeviation_matrix parameters L rho epsilon field low] at sum
  apply sum.congr_fun
  intro cell
  change fourierPhase cell axialAngle * (cellExponential (kappaLaurentFrequency component slot) polarAngle * _) = _
  exact mul_left_comm _ _ _

/-- Full axial Fourier realization at the SAME original physical point:
the cells used in BS40 are exactly kappa-kappa_circle, including the sign
of det F and the distinct domain/physical frame orderings. -/
theorem kappaPolarCell_actual_fourier (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius polarAngle axialAngle : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    HasSum (fun cell => fourierPhase cell axialAngle *
      kappaPolarCell parameters L rho epsilon field low component cell (radius, polarAngle) 0)
      (physicalKappa polarAngle (originalPhysicalSignedCofactor parameters L epsilon field axialAngle
        (polarClosedPoint radius polarAngle nonnegative bounded)) component -
        (![0, -1, 0] : Fin 3 → ℂ) component) := by
  have sum := hasSum_sum (s := Finset.univ) (fun slot _ =>
    kappaPolarCellTerm_fourier parameters L rho epsilon field low component slot
      radius polarAngle axialAngle nonnegative bounded)
  rw [← physicalKappa_laurent, physicalKappa_deviation] at sum
  apply sum.congr_fun
  intro cell
  change fourierPhase cell axialAngle *
    (PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : PhysicalValue 1 →L[ℂ] ℂ)
      ((∑ slot, kappaPolarCellTerm parameters L rho epsilon field low component slot cell) (radius, polarAngle)) = _
  rw [Finset.sum_apply, map_sum, Finset.mul_sum]
  rfl

end Grad.SourceCollarCoefficients
