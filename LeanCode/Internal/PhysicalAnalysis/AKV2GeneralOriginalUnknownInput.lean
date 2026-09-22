import AKV1GeneralOriginalWeightedPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSystem Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularHighGenerators

open Grad.AnnularCurrentLow Grad.AnnularStrongSolution Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

theorem originalPairCurve_coefficient (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode (originalPairCurve parameters lower length positive bounded lengthPositive field grade radius) =
      (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade
          (radialClamp lower bounded.le radius) mode,
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade
          (radialClamp lower bounded.le radius) mode) :=
  Prod.ext
    (sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades grade _ mode)
    (sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades grade _ mode)

theorem conjugatedOriginalPairCurve_physical (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius) =
      Real.exp (radialPhase parameters radius mode.2) • hilbertPairCoefficient mode
        (originalPairCurve parameters lower length positive bounded lengthPositive field grade radius) := by
  rw [originalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades,
    radialClamp_eq lower bounded.le radius inside]
  exact conjugatedOriginalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades grade radius inside mode

omit allGrades in
def generalConjugatedUnknownSevenCurve (grade : ℕ) (radius : ℝ) : CellL2 7 :=
  rawUnknownSevenOperator parameters radius
    (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+2) radius)

theorem generalConjugatedUnknownSevenCurve_physical (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    generalConjugatedUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius mode =
      Real.exp (radialPhase parameters radius mode.2) •
        sameUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius mode :=
  rawUnknownSevenOperator_phase parameters radius _ _ mode _
    (conjugatedOriginalPairCurve_physical parameters lower length positive bounded lengthPositive field allGrades
      (grade+2) radius inside mode)

theorem generalConjugatedUnknownSevenCurve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      generalConjugatedUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade+1) : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field) radius mode) := by
  filter_upwards [sameUnknownCurve_actual parameters lower length positive bounded lengthPositive field allGrades grade,
    ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  rw [generalConjugatedUnknownSevenCurve_physical parameters lower length positive bounded lengthPositive field allGrades
    grade radius inside mode]
  change Real.exp (radialPhase parameters radius mode.2) •
    (rawUnknownSevenOperator parameters radius _ mode) = _
  rw [same mode]
  exact smul_comm _ _ _

end Grad.AnnularGeneralSourceRegularity
