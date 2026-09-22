import AKAA22ActualFullCellFirstDerivative

noncomputable section

set_option maxHeartbeats 1500000

open MeasureTheory Classical
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.WeakTesting Grad.WeakTesting.Commutation

def startupFirstCoordinates {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (field : FieldL2 dimension domain) (derivatives : Fin 2 → FieldL2 dimension domain)
    (index : JetIndex 1) : FieldL2 dimension domain :=
  if index.val = (0, 0) then field else if index.val = (1, 0) then derivatives 0 else derivatives 1

theorem startupFirstCoordinates_weak {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (field : FieldL2 dimension domain) (derivatives : Fin 2 → FieldL2 dimension domain)
    (weak : ∀ direction, HasWeakOrderedDerivative dimension domain 1 (startupFirstWord direction) field (derivatives direction))
    (index : JetIndex 1) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test (startupFirstCoordinates field derivatives index) =
      ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor 0 cell) *
        derivativeTestPairing dimension 1 domain index cell vector test
          (Grad.CellWeights.inverseFieldCLM dimension domain 0
            (startupFirstCoordinates field derivatives (zeroIndex 1))) := by
  rw [Grad.CellWeights.inverseFieldCLM_zero]
  have zero : startupFirstCoordinates field derivatives (zeroIndex 1) = field := by
    simp [startupFirstCoordinates, zeroIndex]
  rw [zero]
  simp only [ContinuousLinearMap.id_apply, Grad.CellWeights.positiveFactor, pow_zero, mul_one]
  rcases index with ⟨⟨first, second⟩, bound⟩
  have cases : (first = 0 ∧ second = 0) ∨ (first = 1 ∧ second = 0) ∨ (first = 0 ∧ second = 1) := by omega
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [startupFirstCoordinates, degree, zero_add, pow_zero, one_mul]
    rfl
  · have word : derivativeWord (⟨(1, 0), bound⟩ : JetIndex 1) = startupFirstWord 0 := by
      funext position
      fin_cases position
      rfl
    have identity := weak 0 cell vector test.toFun test.smooth test.compact test.supported
    change compactPairing dimension domain cell vector test.toFun test.smooth test.compact (derivatives 0) =
      (-1 : ℂ) ^ 1 * orderedDerivativePairing dimension domain cell vector test.toFun test.smooth test.compact 1 (startupFirstWord 0) field at identity
    simpa only [startupFirstCoordinates, if_false, if_true, derivativeTestPairing, testPairing, degree,
      add_zero, word, show (1, 0) ≠ (0, 0) from by decide] using identity
  · have word : derivativeWord (⟨(0, 1), bound⟩ : JetIndex 1) = startupFirstWord 1 := by
      funext position
      fin_cases position
      rfl
    have identity := weak 1 cell vector test.toFun test.smooth test.compact test.supported
    change compactPairing dimension domain cell vector test.toFun test.smooth test.compact (derivatives 1) =
      (-1 : ℂ) ^ 1 * orderedDerivativePairing dimension domain cell vector test.toFun test.smooth test.compact 1 (startupFirstWord 1) field at identity
    simpa only [startupFirstCoordinates, if_false, derivativeTestPairing, testPairing, degree,
      zero_add, word, show (0, 1) ≠ (0, 0) from by decide, show (0, 1) ≠ (1, 0) from by decide] using identity

def startupFirstGraph {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (field : FieldL2 dimension domain) (derivatives : Fin 2 → FieldL2 dimension domain)
    (weak : ∀ direction, HasWeakOrderedDerivative dimension domain 1 (startupFirstWord direction) field (derivatives direction)) :
    GraphGrade dimension 1 0 domain :=
  ofCoordinates dimension 1 domain (fun _ => 0) (startupFirstCoordinates field derivatives)
    (startupFirstCoordinates_weak field derivatives weak)

theorem startupFirstGraph_base {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (field : FieldL2 dimension domain) (derivatives : Fin 2 → FieldL2 dimension domain)
    (weak : ∀ direction, HasWeakOrderedDerivative dimension domain 1 (startupFirstWord direction) field (derivatives direction)) :
    base dimension 1 domain (fun _ => 0) (startupFirstGraph field derivatives weak) = field := by
  rw [base_apply, Grad.CellWeights.inverseFieldCLM_zero]
  change startupFirstCoordinates field derivatives (zeroIndex 1) = field
  simp [startupFirstCoordinates, zeroIndex]

def startupJetZero : JetIndex 1 := ⟨(0, 0), by decide⟩
def startupJetFirst : JetIndex 1 := ⟨(1, 0), by decide⟩
def startupJetSecond : JetIndex 1 := ⟨(0, 1), by decide⟩

theorem startupFirstIndex_enumeration : (Finset.univ : Finset (JetIndex 1)) =
    {startupJetZero, startupJetFirst, startupJetSecond} := by
  ext index
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  have bound := index.property
  have cases : index.val = (0, 0) ∨ index.val = (1, 0) ∨ index.val = (0, 1) := by
    apply (show (index.val.1 = 0 ∧ index.val.2 = 0) ∨ (index.val.1 = 1 ∧ index.val.2 = 0) ∨
      (index.val.1 = 0 ∧ index.val.2 = 1) from by omega).imp
    · rintro ⟨first, second⟩
      exact Prod.ext first second
    · intro cases
      exact cases.imp (fun pair => Prod.ext pair.1 pair.2) (fun pair => Prod.ext pair.1 pair.2)
  rcases cases with same | same | same
  · exact Or.inl (Subtype.ext same)
  · exact Or.inr (Or.inl (Subtype.ext same))
  · exact Or.inr (Or.inr (Subtype.ext same))

theorem startupFirstGraph_norm_sq {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (field : FieldL2 dimension domain) (derivatives : Fin 2 → FieldL2 dimension domain)
    (weak : ∀ direction, HasWeakOrderedDerivative dimension domain 1 (startupFirstWord direction) field (derivatives direction)) :
    ‖startupFirstGraph field derivatives weak‖ ^ 2 =
      ‖field‖ ^ 2 + ‖derivatives 0‖ ^ 2 + ‖derivatives 1‖ ^ 2 := by
  rw [graphGrade_norm_sq, startupFirstIndex_enumeration]
  have firstDistinct : startupJetZero ∉
      ({startupJetFirst, startupJetSecond} : Finset (JetIndex 1)) := by
    intro membership
    rcases Finset.mem_insert.mp membership with equality | membership
    · have coordinate := congrArg (fun index : JetIndex 1 => index.val.1) equality
      change (0 : ℕ) = 1 at coordinate
      omega
    · have coordinate := congrArg (fun index : JetIndex 1 => index.val.2)
        (Finset.mem_singleton.mp membership)
      change (0 : ℕ) = 1 at coordinate
      omega
  have secondDistinct : startupJetFirst ∉
      ({startupJetSecond} : Finset (JetIndex 1)) := by
    intro membership
    have coordinate := congrArg (fun index : JetIndex 1 => index.val.1)
      (Finset.mem_singleton.mp membership)
    change (1 : ℕ) = 0 at coordinate
    omega
  rw [Finset.sum_insert firstDistinct, Finset.sum_insert secondDistinct, Finset.sum_singleton]
  change ‖field‖ ^ 2 + (‖derivatives 0‖ ^ 2 + ‖derivatives 1‖ ^ 2) = _
  exact (add_assoc _ _ _).symm

theorem startup_threeNorm_bound (norm first second third : ℝ)
    (_normNonnegative : 0 ≤ norm) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (thirdNonnegative : 0 ≤ third)
    (square : norm ^ 2 = first ^ 2 + second ^ 2 + third ^ 2) :
    norm ≤ first + second + third := by
  nlinarith only [mul_nonneg firstNonnegative secondNonnegative,
    mul_nonneg firstNonnegative thirdNonnegative, mul_nonneg secondNonnegative thirdNonnegative,
    _normNonnegative, firstNonnegative, secondNonnegative, thirdNonnegative, square]

theorem startupFirstGraph_norm_bound {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (field : FieldL2 dimension domain) (derivatives : Fin 2 → FieldL2 dimension domain)
    (weak : ∀ direction, HasWeakOrderedDerivative dimension domain 1 (startupFirstWord direction) field (derivatives direction)) :
    ‖startupFirstGraph field derivatives weak‖ ≤ ‖field‖ + ‖derivatives 0‖ + ‖derivatives 1‖ :=
  startup_threeNorm_bound _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (startupFirstGraph_norm_sq field derivatives weak)

end Grad.CartesianStartup
