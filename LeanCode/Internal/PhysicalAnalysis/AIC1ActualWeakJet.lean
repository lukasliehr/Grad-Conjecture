import GC18APFaithful
import ZE1Compact

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Grad.InteriorLocalization
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets

/-- The actual AP Cartesian index, with unchanged derivative order. -/
def apJetIndex {grade : ℕ} (index : JetIndex grade) : DerivativeIndex grade :=
  ⟨(⟨index.val.1, by have := index.property; omega⟩,
    ⟨index.val.2, by have := index.property; omega⟩), index.property⟩

/-- One genuine weighted cell of the original completed AP graph, injected
at the auxiliary cell zero in the existing distributional graph. -/
def apCellWeakTuple (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] JetTuple dimension grade openUnitDisk :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : JetIndex grade => FieldL2 dimension openUnitDisk)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun index =>
      (apDiskInjection dimension).comp (apUnscaledCoordinate L sigma gamma ell cell (apJetIndex index))))

@[simp] theorem apCellWeakTuple_apply (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) (index : JetIndex grade) :
    apCellWeakTuple L sigma gamma ell dimension grade cell field index =
      apDiskInjection dimension (apUnscaledCoordinate L sigma gamma ell cell (apJetIndex index) field) := rfl

theorem apCellWeakTuple_mem (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    apCellWeakTuple L sigma gamma ell dimension grade cell field ∈
      jetGraph dimension grade openUnitDisk (fun _ => 0) := by
  apply (jetGraph_mem dimension grade openUnitDisk (fun _ => 0) _).mpr
  intro index testCell vector test
  have weak := apCompleted_weak L sigma gamma ell cell (apJetIndex index) field
    testCell vector test.toFun test.smooth test.compact test.supported
  simp only [Grad.CellWeights.positiveFactor, pow_zero, mul_one,
    ambientBase_apply, Grad.CellWeights.inverseFieldCLM_zero,
    ContinuousLinearMap.id_apply, apCellWeakTuple_apply]
  exact weak

/-- No new derivative coordinates are assumed: the existing compact-test
proof shows that every actual AP cell lies in the genuine weak graph. -/
def apCellWeakJet (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ]
      WJet dimension grade openUnitDisk (fun _ => 0) :=
  (apCellWeakTuple L sigma gamma ell dimension grade cell).codRestrict _
    (apCellWeakTuple_mem L sigma gamma ell dimension grade cell)

theorem apCellWeakJet_base (L sigma gamma ell : ℝ) (dimension grade : ℕ) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    base dimension grade openUnitDisk (fun _ => 0)
      (apCellWeakJet L sigma gamma ell dimension grade cell field) =
      apDiskInjection dimension (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) field) := by
  change Grad.CellWeights.inverseFieldCLM dimension openUnitDisk 0
    (apCellWeakTuple L sigma gamma ell dimension grade cell field (zeroIndex grade)) = _
  rw [Grad.CellWeights.inverseFieldCLM_zero, ContinuousLinearMap.id_apply]
  rfl

end Grad.InteriorLocalization
