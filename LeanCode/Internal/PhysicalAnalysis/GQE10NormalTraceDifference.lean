import GQE9PhysicalNormalRow

noncomputable section
set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

theorem linear_trace_difference {E T : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup T] [Module ℂ T] (trace : E →ₗ[ℂ] T) (first reference output error : E)
    (product : output = first + error) (preserved : trace first = trace reference) :
    trace output - trace reference = trace error := by
  rw [product, map_add, preserved]
  abel

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

def completedNormalTrace (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  ((apHighTrace L sigma gamma ell (grade + 1) (by omega)).comp
    (apMultiplier admissible (normalRowFamily data (grade + 1)))).comp (completedReconstruct admissible grade core)

def completedReferenceTrace (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
  (apHighTrace L sigma gamma ell (grade + 1) (by omega)).comp (completedRadial admissible grade core)

theorem completedNormalTrace_difference (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    completedNormalTrace admissible data grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
        (completedTransfer smooth grade large field) -
      completedReferenceTrace admissible grade (circularCompensatedCore admissible) field =
      apHighTrace L sigma gamma ell (grade + 1) (by omega)
        (apMultiplier admissible (data.traceDeviation (grade + 1))
          (completedReconstruct admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
            (completedTransfer smooth grade large field))) := by
  let output := completedReconstruct admissible grade
    (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent) (completedTransfer smooth grade large field)
  let source := completedReconstruct admissible grade (circularCompensatedCore admissible) field
  let trace : apGrade L sigma gamma ell 1 (grade + 1) →L[ℂ]
      APBoundaryGrade L sigma gamma ell 1 (grade + 1) :=
    apHighTrace L sigma gamma ell (grade + 1) (by omega)
  apply linear_trace_difference trace.toLinearMap (apRadialContraction admissible (grade + 1) output)
    (apRadialContraction admissible (grade + 1) source)
    (apMultiplier admissible (normalRowFamily data (grade + 1)) output)
    (apMultiplier admissible (data.traceDeviation (grade + 1)) output)
  · exact congrArg (fun mapping : apGrade L sigma gamma ell 3 (grade + 1) →L[ℂ]
        apGrade L sigma gamma ell 1 (grade + 1) => mapping output)
      (apMultiplier_add admissible (referenceRowFamily L sigma gamma ell (grade + 1)) (data.traceDeviation (grade + 1)))
  · exact congrArg trace (completedRadial_transfer smooth grade large field)

/-- Exact AO25 on every point of the specified completed circular
domain: the row difference is multiplied in the bulk before the trace. -/
theorem completedNormalTrace_difference_Qa (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    completedNormalTrace admissible data grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
        (completedTransfer smooth grade large field) -
      completedReferenceTrace admissible grade (circularCompensatedCore admissible) field =
      apHighTrace L sigma gamma ell (grade + 1) (by omega)
        (apMultiplier admissible
          (normalRowFamily data (grade + 1) - referenceRowFamily L sigma gamma ell (grade + 1))
          (Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible data.gaugeDeviation (grade + 1)
            (completedReconstruct admissible grade (circularCompensatedCore admissible) field))) := by
  exact (completedNormalTrace_difference admissible data smooth grade large field).trans
    (congrArg₂ (fun coefficient : Coefficient L sigma gamma ell (grade + 1) 3 1 =>
      fun vector : apGrade L sigma gamma ell 3 (grade + 1) =>
        apHighTrace L sigma gamma ell (grade + 1) (by omega) (apMultiplier admissible coefficient vector))
      (normalRowFamily_sub_reference data (grade + 1)).symm
      (completedReconstruct_transfer admissible smooth grade large field))

theorem completedNormalTrace_difference_bound (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    ‖completedNormalTrace admissible data grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
        (completedTransfer smooth grade large field) -
      completedReferenceTrace admissible grade (circularCompensatedCore admissible) field‖ ≤
      (Real.sqrt (traceCellConstant (grade + 1)) * apMultiplierConstant L sigma gamma (grade + 1)) *
        ‖data.traceDeviation (grade + 1)‖ *
          ‖completedReconstruct admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
            (completedTransfer smooth grade large field)‖ := by
  have normEquality := congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => ‖value‖)
    (completedNormalTrace_difference admissible data smooth grade large field)
  exact normEquality.le.trans (apHighMultiplierTrace_bound admissible (by omega) (data.traceDeviation (grade + 1)) _)

end Grad.GaugeCoefficients.Physical.Compensated
