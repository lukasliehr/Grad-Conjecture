import AKR17AllOriginalRetainedTupleCoefficients
import AKC29OriginalPhysicalRowConjugatedRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (tuple : OriginalSmoothTuple parameters lower)

def tupleConjugatedTangential (slot : Fin 4) (axis : Bool) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  hilbertFrequencyOperator parameters 1 (some axis) (tupleWeightedCurve parameters lower tuple slot (grade+1) radius)

theorem tupleConjugatedTangential_smooth (slot : Fin 4) (axis : Bool) (grade : ℕ) :
    ContDiffOn ℝ ∞ (tupleConjugatedTangential parameters lower tuple slot axis grade) (Icc lower 1) :=
  (hilbertFrequencyOperator parameters 1 (some axis)).restrictScalars ℝ |>.contDiff.comp_contDiffOn
    (tupleWeightedCurve_smooth parameters lower tuple slot (grade+1))

theorem tupleConjugatedTangential_coefficient (slot : Fin 4) (axis : Bool) (grade : ℕ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    tupleConjugatedTangential parameters lower tuple slot axis grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          (frequencyNumerator (some axis) mode • originalPhysicalCoefficient (tuple.val slot) radius mode)) := by
  rw [tupleConjugatedTangential,hilbertFrequencyOperator_apply,tupleWeightedCurve_coefficient parameters lower tuple slot
    (grade+1) radius inside mode]
  change frequencyRatioSymbol (some axis) mode •
    ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ (grade+1) : ℝ) : ℂ) •
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        originalPhysicalCoefficient (tuple.val slot) radius mode) = _
  rw [frequencyRatio_weighted]
  rw [smul_comm (frequencyNumerator (some axis) mode)]
  rfl

/-- All seven original normalized tuple slots at the SAME phase and grade. -/
def tupleConjugatedSevenCurve (grade : ℕ) (radius : ℝ) : CellL2 7 :=
  (((((hilbertSlotInjection parameters 0 (tupleConjugatedTangential parameters lower tuple 0 false grade radius) +
    (radius : ℂ)⁻¹ • hilbertSlotInjection parameters 1 (tupleConjugatedTangential parameters lower tuple 1 false grade radius)) +
    hilbertSlotInjection parameters 2 (tupleConjugatedTangential parameters lower tuple 1 true grade radius)) +
    (radius : ℂ)⁻¹ • hilbertSlotInjection parameters 3 (tupleWeightedCurve parameters lower tuple 1 grade radius)) +
    hilbertSlotInjection parameters 4 (tupleWeightedCurve parameters lower tuple 2 grade radius)) +
    hilbertSlotInjection parameters 5 (tupleConjugatedTangential parameters lower tuple 2 false grade radius)) +
    hilbertSlotInjection parameters 6 (tupleWeightedCurve parameters lower tuple 3 grade radius)

include positive in
theorem tupleConjugatedSevenCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (tupleConjugatedSevenCurve parameters lower tuple grade) (Icc lower 1) := by
  have injected (slot : Fin 7) (field : Fin 4) :=
    (hilbertSlotInjection parameters slot).restrictScalars ℝ |>.contDiff.comp_contDiffOn
      (tupleWeightedCurve_smooth parameters lower tuple field grade)
  have differentiated (slot : Fin 7) (field : Fin 4) (axis : Bool) :=
    (hilbertSlotInjection parameters slot).restrictScalars ℝ |>.contDiff.comp_contDiffOn
      (tupleConjugatedTangential_smooth parameters lower tuple field axis grade)
  exact ((((((differentiated 0 0 false).add ((reciprocalRadius_smooth lower positive).smul
    (differentiated 1 1 false))).add (differentiated 2 1 true)).add
    ((reciprocalRadius_smooth lower positive).smul (injected 3 1))).add (injected 4 2)).add
    (differentiated 5 2 false)).add (injected 6 3)

theorem tupleConjugatedSevenCurve_coefficient (grade : ℕ) (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    tupleConjugatedSevenCurve parameters lower tuple grade radius.val mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
          originalTupleNormalizedCoefficient parameters lower tuple radius mode) := by
  have injection (slot : Fin 7) (input : CellL2 1) :
      hilbertSlotInjection parameters slot input mode = matrixUnit slot 0 (input mode) := rfl
  change (((((hilbertSlotInjection parameters 0 _ mode +
    (radius.val : ℂ)⁻¹ • hilbertSlotInjection parameters 1 _ mode) + hilbertSlotInjection parameters 2 _ mode) +
    (radius.val : ℂ)⁻¹ • hilbertSlotInjection parameters 3 _ mode) + hilbertSlotInjection parameters 4 _ mode) +
    hilbertSlotInjection parameters 5 _ mode) + hilbertSlotInjection parameters 6 _ mode = _
  simp only [injection,tupleConjugatedTangential_coefficient parameters lower tuple _ _ _ radius.val radius.property,
    tupleWeightedCurve_coefficient parameters lower tuple _ _ radius.val radius.property, map_smul]
  ext slot
  fin_cases slot <;> simp [originalTupleNormalizedCoefficient,matrixUnit_apply,operatorBasis,smul_smul] <;> ring

end Grad.AnnularOriginalCoreRealization
