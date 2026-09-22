import QuotientProductLinearity

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

/-- Constant-in-cell insertion into the original phase-weighted core. -/
theorem singleton_mem_originalCore {dimension : ℕ} (parameters : PhaseParameters)
    (jet : ClosedJet dimension) :
    (fun cell : ℤ => if cell = 0 then jet else 0) ∈
      originalCoreSubmodule parameters dimension := by
  intro grade
  rw [memlp_iff_summable_sq]
  apply ((hasSum_ite_eq (0 : ℤ)
    (‖cellGradeRowLinear (grade := grade) parameters 0 jet‖ ^ 2)).summable).congr
  intro cell
  by_cases zeroCell : cell = 0
  · subst zeroCell
    simp [rawCartesianGradeCoordinates]
  · simp [rawCartesianGradeCoordinates, zeroCell]

/-- One closed jet placed at the constant cell mode, zero at every other cell. -/
def singletonCore (parameters : PhaseParameters) {dimension : ℕ} (jet : ClosedJet dimension) :
    ACore parameters dimension :=
  ⟨fun cell => if cell = 0 then jet else 0, singleton_mem_originalCore parameters jet⟩

theorem singletonCore_val {dimension : ℕ} (jet : ClosedJet dimension) (cell : ℤ) :
    (singletonCore parameters jet).val cell = if cell = 0 then jet else 0 := rfl

/-- The constant closed jet with one fixed value. -/
def constantValueJet {dimension : ℕ} (vector : ComplexEuclidean dimension) : ClosedJet dimension :=
  globalClosedJet (fun _ => vector) contDiff_const

@[simp] theorem constantValueJet_value {dimension : ℕ} (vector : ComplexEuclidean dimension)
    (point : ClosedDisk) : (constantValueJet vector).value point = vector :=
  globalClosedJet_value (fun _ => vector) contDiff_const point

/-- The constant physical field: one vector at the constant cell mode. -/
def constantCore (parameters : PhaseParameters) {dimension : ℕ}
    (vector : ComplexEuclidean dimension) : ACore parameters dimension :=
  singletonCore parameters (constantValueJet vector)

theorem constantCore_value_zero {dimension : ℕ} (vector : ComplexEuclidean dimension)
    (point : ClosedDisk) :
    ((constantCore parameters vector).val 0).value point = vector := by
  change ((if (0 : ℤ) = 0 then constantValueJet vector else 0).value point) = vector
  rw [if_pos rfl, constantValueJet_value]

theorem constantCore_value_ne {dimension : ℕ} (vector : ComplexEuclidean dimension)
    {cell : ℤ} (nonzero : cell ≠ 0) (point : ClosedDisk) :
    ((constantCore parameters vector).val cell).value point = 0 := by
  change ((if cell = 0 then constantValueJet vector else 0).value point) = 0
  rw [if_neg nonzero, closedJet_value_zero]
  rfl

/-- The fixed constant field `e_T` of the affine state derivative. -/
def eTConstantCore (parameters : PhaseParameters) : ACore parameters 3 :=
  constantCore parameters (EuclideanSpace.single 1 1)

/-- A constant scalar field in the one-dimensional coefficient space. -/
def scalarConstantCore (parameters : PhaseParameters) (scalar : ℂ) : ACore parameters 1 :=
  constantCore parameters (EuclideanSpace.single 0 scalar)

end Grad.NonlinearQuotientBounds
