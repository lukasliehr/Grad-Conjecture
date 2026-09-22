import AFZ1HighMeanFreeTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 150000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

theorem linearMeanDefect_identity {E T : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup T] [Module ℂ T] (trace : E →ₗ[ℂ] T) (meanFree : E →ₗ[ℂ] E)
    (meanLaw : ∀ value, trace (meanFree value) = trace value)
    (primitive normal radial first second cross : E)
    (primitiveLaw : primitive = -meanFree radial + meanFree (first + cross))
    (normalLaw : normal = radial + second) :
    trace primitive + trace normal = trace (first + second + cross) := by
  rw [primitiveLaw, normalLaw, map_add, map_neg, meanLaw, meanLaw, map_add, map_add, map_add, map_add]
  abel

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

/-- Every AR16 coefficient correction, including the retained cross term. -/
def apMatchingDefectBulk (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (vector : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    apGrade L sigma gamma ell 1 grade :=
  apRadialContraction admissible grade (apMultiplier admissible (data.fluxDeviation grade) vector) +
    apMultiplier admissible (data.traceDeviation grade) vector +
    apTangentContraction admissible grade
      (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi))

theorem normalBulk_decomposition (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (vector : apGrade L sigma gamma ell 3 grade) :
    apMultiplier admissible (normalRowFamily data grade) vector =
      apRadialContraction admissible grade vector + apMultiplier admissible (data.traceDeviation grade) vector :=
  congrArg (fun mapping : apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 1 grade => mapping vector)
    (apMultiplier_add admissible (referenceRowFamily L sigma gamma ell grade) (data.traceDeviation grade))

/-- Exact AR16 before inserting a native graph element. -/
theorem apMatchingDefect_trace (data : LedgerData L sigma gamma ell) (grade : ℕ) (positive : 1 ≤ grade)
    (vector : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    apHighTrace L sigma gamma ell grade positive (apMatchingPrimitive admissible data grade vector psi) +
      apHighTrace L sigma gamma ell grade positive (apMultiplier admissible (normalRowFamily data grade) vector) =
        apHighTrace L sigma gamma ell grade positive (apMatchingDefectBulk admissible data grade vector psi) :=
  linearMeanDefect_identity (apHighTrace L sigma gamma ell grade positive).toLinearMap
    (apMeanFree L sigma gamma ell 1 grade).toLinearMap (apHighTrace_meanFree L sigma gamma ell grade positive)
    (apMatchingPrimitive admissible data grade vector psi) (apMultiplier admissible (normalRowFamily data grade) vector)
    (apRadialContraction admissible grade vector)
    (apRadialContraction admissible grade (apMultiplier admissible (data.fluxDeviation grade) vector))
    (apMultiplier admissible (data.traceDeviation grade) vector)
    (apTangentContraction admissible grade
      (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi)))
    (apMatchingPrimitive_deviation admissible data grade vector psi) (normalBulk_decomposition admissible data grade vector)

def completedMatchingDefectBulk (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 1) :=
  (((apRadialContraction admissible (grade + 1)).comp (apMultiplier admissible (data.fluxDeviation (grade + 1))) +
    apMultiplier admissible (data.traceDeviation (grade + 1))).comp (completedReconstruct admissible grade core)) +
  (((apTangentContraction admissible (grade + 1)).comp (apMultiplier admissible (data.fluxDeviation (grade + 1)))).comp
    (apMatchingRadialColumn admissible (grade + 1))).comp (completedPsi admissible grade core)

/-- The actual high defect e=Qp+b; the physical normal row remains present. -/
def completedMatchingDefect (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  (apHighProjection L sigma gamma ell (grade + 1)).comp (completedMatchingP admissible data grade core) +
    completedNormalTrace admissible data grade core

/-- Exact signed AR16 on the original completed graph, with all three
coefficient-error products formed in the bulk before taking the high trace. -/
theorem completedMatchingDefect_formula (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    completedMatchingDefect admissible data grade core field =
      apHighTrace L sigma gamma ell (grade + 1) (by omega)
        (completedMatchingDefectBulk admissible data grade core field) :=
  apMatchingDefect_trace admissible data (grade + 1) (by omega)
    (completedReconstruct admissible grade core field) (completedPsi admissible grade core field)

theorem completedMatchingDefect_high (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    apHighProjection L sigma gamma ell (grade + 1) (completedMatchingDefect admissible data grade core field) =
      completedMatchingDefect admissible data grade core field := by
  have formula := completedMatchingDefect_formula admissible data grade core field
  exact (congrArg (apHighProjection L sigma gamma ell (grade + 1)) formula).trans
    ((apHighProjection_idempotent L sigma gamma ell (grade + 1)
      (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedMatchingDefectBulk admissible data grade core field))).trans formula.symm)

end Grad.GaugeCoefficients.Physical.Compensated
