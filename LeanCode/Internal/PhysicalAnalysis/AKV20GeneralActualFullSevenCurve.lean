import AKV19ActualCartesianWeightedRadialSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularHighGenerators Grad.AnnularCurrentLow
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularKnownLow Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)

/-- The actual full normalized seven packet, with the prescribed sources
inserted exactly once and the original phase and frequency grade. -/
def generalConjugatedFullSevenCurve (grade : ℕ) (radius : ℝ) : CellL2 7 :=
  generalConjugatedUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius +
    curves.seven (grade+1) radius

theorem generalConjugatedFullSevenCurve_continuous
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted) (grade : ℕ) :
    ContinuousOn (generalConjugatedFullSevenCurve parameters lower length positive bounded lengthPositive data field curves grade) (Icc lower 1) := by
  exact (((rawUnknownSevenOperator_smooth parameters lower positive).continuousOn.clm_apply
    (conjugatedOriginalPairCurve_continuous parameters lower length positive bounded lengthPositive field allGrades (grade+2)).continuousOn).add
      (curves.sevenSmooth (grade+1)).continuousOn)

theorem generalConjugatedFullSevenCurve_smooth
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1)) (grade : ℕ) :
    ContDiffOn ℝ ∞ (generalConjugatedFullSevenCurve parameters lower length positive bounded lengthPositive data field curves grade) (Icc lower 1) := by
  have operator := ((ContinuousLinearMap.restrictScalarsIsometry ℂ PhysicalHilbertPair (CellL2 7) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn
    (rawUnknownSevenOperator_smooth parameters lower positive)
  exact (operator.clm_apply (smooth (grade+2))).add (curves.sevenSmooth (grade+1))

theorem generalConjugatedFullSevenCurve_actual
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      generalConjugatedFullSevenCurve parameters lower length positive bounded lengthPositive data field curves grade radius mode =
        (annularFrequency mode.1 mode.2 : ℂ)^(grade+1) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field) radius mode) := by
  rw [fullStrongSevenInput_split]
  filter_upwards [generalConjugatedUnknownSevenCurve_actual parameters lower length positive bounded lengthPositive field allGrades grade,
    curves.sevenSame (grade+1), lowRhoPhysicalCoefficient_add_ae parameters lower positive
      (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)
      (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data))] with radius unknown known added
  intro mode
  change generalConjugatedUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius mode +
    curves.seven (grade+1) radius mode = _
  rw [unknown mode,known mode,added mode,smul_add,smul_add]
  rfl

end Grad.AnnularGeneralSourceRegularity
