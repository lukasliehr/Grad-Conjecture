import SCC14FourierAngularShift

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.SourceCollarAngular

def scalarRowMapping (row : Fin 3 → ℂ) : OperatorValue 3 1 :=
  matrixOperator (fun _ column => row column)

theorem scalarRowMapping_apply (row : Fin 3 → ℂ) (value : PhysicalValue 3) :
    scalarRowMapping row value 0 = ∑ index : Fin 3, row index * value index := by
  simp [scalarRowMapping, matrixOperator, Fintype.sum_prod_type,
    Fin.sum_univ_three, matrixUnit, columnEmbedding_apply, operatorBasis]

theorem operatorMatrix_mulVec {input output : ℕ} (value : OperatorValue input output)
    (column : PhysicalValue input) : (operatorMatrix value).mulVec (fun index => column index) =
      fun index => value column index := by
  funext row
  change (∑ index, operatorMatrix value row index * column index) = value column row
  conv_rhs => rw [← operatorBasis_expansion column, map_sum]
  change (∑ index, operatorMatrix value row index * column index) =
    (PiLp.proj 2 (fun _ : Fin output => ℂ) row : PhysicalValue output →L[ℂ] ℂ)
      (∑ index, value (column index • operatorBasis index))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_smul]
  change _ = column index * value (operatorBasis index) row
  exact mul_comm _ _

theorem scalarRowMapping_pairing (row : Fin 3 → ℂ) (value : OperatorValue 3 3)
    (column : PhysicalValue 3) :
    scalarRowMapping row (value column) 0 = matrixPairing row (operatorMatrix value) (fun index => column index) := by
  rw [scalarRowMapping_apply, matrixPairing, operatorMatrix_mulVec]
  rfl

def polarLaurentSign (index : Fin 2) : ℤ := if index = 0 then 1 else -1

def radialLaurentVector (index : Fin 2) : Fin 3 → ℂ :=
  ![(2 : ℂ)⁻¹, if index = 0 then -Complex.I / 2 else Complex.I / 2, 0]

def tangentialLaurentVector (index : Fin 2) : Fin 3 → ℂ :=
  ![if index = 0 then Complex.I / 2 else -Complex.I / 2, (2 : ℂ)⁻¹, 0]

theorem radialLaurentVector_sum (angle : ℝ) (coordinate : Fin 3) :
    ∑ index : Fin 2, cellExponential (polarLaurentSign index) angle * radialLaurentVector index coordinate =
      physicalRadialVector angle coordinate := by
  fin_cases coordinate <;>
    simp [Fin.sum_univ_two, polarLaurentSign, radialLaurentVector, physicalRadialVector,
      cellExponential_one, cellExponential_neg_one]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem tangentialLaurentVector_sum (angle : ℝ) (coordinate : Fin 3) :
    ∑ index : Fin 2, cellExponential (polarLaurentSign index) angle * tangentialLaurentVector index coordinate =
      physicalTangentialVector angle coordinate := by
  fin_cases coordinate <;>
    simp [Fin.sum_univ_two, polarLaurentSign, tangentialLaurentVector, physicalTangentialVector,
      cellExponential_one, cellExponential_neg_one]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

/-- Four slots per component; the last component has one zero second slot.
All slots are fixed scalar/vector contractions and angular shifts. -/
def kappaLaurentRight (component : Fin 3) (index : Fin 2) : PhysicalValue 3 :=
  WithLp.toLp 2 (if component = 0 then radialLaurentVector index
    else if component = 1 then tangentialLaurentVector index
    else if index = 0 then physicalToroidalVector else 0)

def kappaLaurentFrequency (component : Fin 3) (slot : Fin 2 × Fin 2) : ℤ :=
  polarLaurentSign slot.1 + if component = 2 then 0 else polarLaurentSign slot.2

theorem cellExponential_add (first second : ℤ) (angle : ℝ) :
    cellExponential (first + second) angle =
      cellExponential first angle * cellExponential second angle := (cellExponential_mul first second angle).symm

theorem cellExponential_zero (angle : ℝ) : cellExponential 0 angle = 1 := by simp [cellExponential]

theorem physicalKappa_laurent (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ)
    (component : Fin 3) :
    physicalKappa angle matrix component =
      ∑ slot : Fin 2 × Fin 2, cellExponential (kappaLaurentFrequency component slot) angle *
        matrixPairing (tangentialLaurentVector slot.1) matrix
          (fun index => kappaLaurentRight component slot.2 index) := by
  rw [Fintype.sum_prod_type]
  fin_cases component <;>
    simp only [kappaLaurentFrequency, cellExponential_add, kappaLaurentRight] <;>
    simp [Fin.sum_univ_two, physicalKappa, matrixPairing, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, polarLaurentSign, tangentialLaurentVector, radialLaurentVector,
      physicalRadialVector, physicalTangentialVector, physicalToroidalVector,
      cellExponential_one, cellExponential_neg_one, cellExponential_zero]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

end Grad.SourceCollarCoefficients
