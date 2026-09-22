import AKCC16SameFixedAllOrderGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered

theorem startupDerivativePairing_inverse (dimension order weight : ℕ) (index : JetIndex order)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction openUnitDisk)
    (field : StartupL2 dimension) :
    derivativeTestPairing dimension order openUnitDisk index cell vector test
      (Grad.CellWeights.inverseFieldCLM dimension openUnitDisk weight field) =
      Grad.CellWeights.inverseFactor weight cell *
        derivativeTestPairing dimension order openUnitDisk index cell vector test field := by
  rw [derivativeTestPairing_apply, derivativeTestPairing_apply]
  calc
    _ = ∫ point in openUnitDisk, Grad.CellWeights.inverseFactor weight cell •
        (Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
          inner ℂ vector (field point cell)) := by
      apply integral_congr_ae
      filter_upwards [Grad.CellWeights.inverseFieldCLM_coordinate dimension openUnitDisk weight field] with point coordinates
      rw [coordinates cell, inner_smul_right]
      exact smul_comm
        (Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point)
        (Grad.CellWeights.inverseFactor weight cell) (inner ℂ vector (field point cell))
    _ = _ := integral_smul _ _

theorem startupConstantGraph_residual {dimension order : ℕ} (weight : ℕ)
    (tuple : JetTuple dimension order openUnitDisk) (index : JetIndex order)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction openUnitDisk) :
    ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor weight cell) *
      derivativeTestPairing dimension order openUnitDisk index cell vector test
        (Grad.CellWeights.inverseFieldCLM dimension openUnitDisk weight (tuple (zeroIndex order))) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order openUnitDisk index cell vector test
        (tuple (zeroIndex order)) := by
  rw [startupDerivativePairing_inverse]
  calc
    _ = (-1 : ℂ) ^ degree index *
        (Grad.CellWeights.inverseFactor weight cell * Grad.CellWeights.positiveFactor weight cell) *
        derivativeTestPairing dimension order openUnitDisk index cell vector test (tuple (zeroIndex order)) := by ring
    _ = _ := by rw [Grad.WeightedJets.Realization.inverse_positiveFactor, mul_one]

theorem startupConstantGraph_iff {dimension order : ℕ} (weight : ℕ)
    (tuple : JetTuple dimension order openUnitDisk) :
    tuple ∈ jetGraph dimension order openUnitDisk (fun _ => weight) ↔
      tuple ∈ jetGraph dimension order openUnitDisk (fun _ => 0) := by
  rw [jetGraph_mem, jetGraph_mem]
  simp only [ambientBase_apply, startupConstantGraph_residual]

def startupGraphRemoveWeight {dimension order weight : ℕ}
    (field : GraphGrade dimension order weight openUnitDisk) : GraphGrade dimension order 0 openUnitDisk :=
  ⟨field.val, (startupConstantGraph_iff weight field.val).mp field.property⟩

def startupGraphRestoreWeight {dimension order : ℕ} (weight : ℕ)
    (field : GraphGrade dimension order 0 openUnitDisk) : GraphGrade dimension order weight openUnitDisk :=
  ⟨field.val, (startupConstantGraph_iff weight field.val).mpr field.property⟩

theorem startupGraphRemoveWeight_base {dimension order weight : ℕ}
    (field : GraphGrade dimension order weight openUnitDisk) :
    base dimension order openUnitDisk (fun _ => 0) (startupGraphRemoveWeight field) =
      field.val (zeroIndex order) := by
  rw [base_apply, Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
  rfl

theorem startupGraphRestoreWeight_base {dimension order : ℕ} (weight : ℕ)
    (field : GraphGrade dimension order 0 openUnitDisk) :
    base dimension order openUnitDisk (fun _ => weight) (startupGraphRestoreWeight weight field) =
      Grad.CellWeights.inverseFieldCLM dimension openUnitDisk weight
        (base dimension order openUnitDisk (fun _ => 0) field) := by
  rw [base_apply, base_apply, Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
  rfl

end Grad.CartesianStartup
