import GC17InverseRealization
import GC17SeedInverse

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def operatorBasis {dimension : ℕ} (column : Fin dimension) : PhysicalValue dimension :=
  WithLp.toLp 2 fun index => if index = column then 1 else 0

theorem operatorBasis_expansion {dimension : ℕ} (value : PhysicalValue dimension) :
    (∑ column : Fin dimension, value column • operatorBasis column) = value := by
  apply PiLp.ext
  intro row
  change (PiLp.proj 2 (fun _ : Fin dimension => ℂ) row : PhysicalValue dimension →L[ℂ] ℂ)
    (∑ column : Fin dimension, value column • operatorBasis column) = value row
  rw [map_sum]
  simp [operatorBasis]

theorem operatorMatrix_add {input output : ℕ} (first second : OperatorValue input output) :
    operatorMatrix (first + second) = operatorMatrix first + operatorMatrix second := rfl

theorem operatorMatrix_sub {input output : ℕ} (first second : OperatorValue input output) :
    operatorMatrix (first - second) = operatorMatrix first - operatorMatrix second := rfl

theorem operatorMatrix_smul {input output : ℕ} (scalar : ℂ) (value : OperatorValue input output) :
    operatorMatrix (scalar • value) = scalar • operatorMatrix value := rfl

theorem operatorMatrix_one (dimension : ℕ) :
    operatorMatrix (ContinuousLinearMap.id ℂ (PhysicalValue dimension)) = 1 := by
  ext row column
  simp [operatorMatrix, Matrix.one_apply]

theorem operatorMatrix_comp {input middle output : ℕ}
    (outer : OperatorValue middle output) (inner : OperatorValue input middle) :
    operatorMatrix (outer.comp inner) = operatorMatrix outer * operatorMatrix inner := by
  ext row column
  change outer (inner (operatorBasis column)) row =
    ∑ position : Fin middle, outer (operatorBasis position) row * inner (operatorBasis column) position
  calc
    _ = outer (∑ position : Fin middle,
        inner (operatorBasis column) position • operatorBasis position) row :=
      congrArg (fun value : PhysicalValue middle => outer value row)
        (operatorBasis_expansion (inner (operatorBasis column))).symm
    _ = _ := by
      rw [map_sum]
      change (PiLp.proj 2 (fun _ : Fin output => ℂ) row : PhysicalValue output →L[ℂ] ℂ)
        (∑ position : Fin middle, outer (inner (operatorBasis column) position • operatorBasis position)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro position _
      rw [map_smul]
      change inner (operatorBasis column) position * outer (operatorBasis position) row = _
      ring

theorem operatorMatrix_injective {input output : ℕ} :
    Function.Injective (@operatorMatrix input output) := by
  intro first second same
  apply ContinuousLinearMap.ext
  intro value
  rw [← operatorBasis_expansion value, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro column _
  rw [map_smul, map_smul]
  congr 1
  apply PiLp.ext
  intro row
  exact congrFun (congrFun same row) column

def matrixUnit {input output : ℕ} (row : Fin output) (column : Fin input) : OperatorValue input output :=
  columnEmbedding input output column (operatorBasis row)

theorem matrixUnit_apply {input output : ℕ} (row : Fin output) (column : Fin input)
    (value : PhysicalValue input) : matrixUnit row column value = value column • operatorBasis row := rfl

theorem operatorMatrix_matrixUnit {input output : ℕ} (row : Fin output) (column : Fin input) :
    operatorMatrix (matrixUnit row column) = Matrix.single row column 1 := by
  ext otherRow otherColumn
  simp [operatorMatrix, matrixUnit, columnEmbedding_apply, operatorBasis, Matrix.single_apply]
  split_ifs <;> simp_all [eq_comm]

theorem actualFrameInverse_matrix_identity {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3)
    (baseBound : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let frame := physicalFrameMatrix parameters L ell epsilon field angle point
    let inverse := operatorMatrix (coefficientPhysicalValue
      (actualFrameInverse parameters admissible epsilon field grade) angle point)
    frame * inverse = 1 ∧ inverse * frame = 1 := by
  have identities := actualFrameInverse_two_sided parameters admissible epsilon field baseBound grade angle point
  exact ⟨(operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.1).trans (operatorMatrix_one 3)),
    (operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.2).trans (operatorMatrix_one 3))⟩

theorem actualSeedInverse_matrix_identity {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (rho alpha delta parameter : ℝ)
    (baseBound : ‖Grad.GaugeCoefficients.Physical.InverseAllocation.seedInverseInput
      admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let seed := physicalSeedMatrix rho alpha delta parameter angle
    let inverse := operatorMatrix (coefficientPhysicalValue
      (actualSeedInverse admissible rho alpha delta parameter grade) angle point)
    seed * inverse = 1 ∧ inverse * seed = 1 := by
  have identities := actualSeedInverse_two_sided admissible rho alpha delta parameter baseBound grade angle point
  exact ⟨(operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.1).trans (operatorMatrix_one 2)),
    (operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.2).trans (operatorMatrix_one 2))⟩

end Grad.GaugeCoefficients.Physical.Ledger
