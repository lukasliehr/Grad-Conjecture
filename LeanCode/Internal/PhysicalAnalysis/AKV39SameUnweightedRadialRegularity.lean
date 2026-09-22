import AKV38ExactInversePhaseRadialRecovery
import AKV2GeneralOriginalUnknownInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators Grad.PhaseAlgebra
open Grad.AnnularCoupledInverse Grad.AnnularCrossOrbit Grad.AnnularWeightedSmoothness

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))

include allGrades smooth

theorem originalPairCurve_smooth_of_conjugated :
    ∀ grade, ContDiffOn ℝ ∞
      (originalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1) := by
  have same (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
      hilbertPairCoefficient mode (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+reserve) radius) =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ)^reserve •
        (Real.exp (radialPhase parameters radius mode.2) • hilbertPairCoefficient mode
          (originalPairCurve parameters lower length positive bounded lengthPositive field grade radius)) := by
    rw [conjugatedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive field allGrades grade reserve radius inside mode,
      conjugatedOriginalPairCurve_physical parameters lower length positive bounded lengthPositive field allGrades grade radius inside mode]
    rfl
  have first := inversePhaseCurve_smooth_of_weighted parameters lower positive bounded
    (fun grade radius => (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius).1)
    (fun grade radius => (originalPairCurve parameters lower length positive bounded lengthPositive field grade radius).1)
    (fun grade => (smooth grade).fst) (fun grade reserve radius inside mode => by
      have h := congrArg Prod.fst (same grade reserve radius inside mode)
      exact h)
  have second := inversePhaseCurve_smooth_of_weighted parameters lower positive bounded
    (fun grade radius => (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius).2)
    (fun grade radius => (originalPairCurve parameters lower length positive bounded lengthPositive field grade radius).2)
    (fun grade => (smooth grade).snd) (fun grade reserve radius inside mode => by
      have h := congrArg Prod.snd (same grade reserve radius inside mode)
      exact h)
  intro grade
  exact (first grade).prodMk (second grade)

end Grad.AnnularGeneralSourceRegularity
