import AKD2SameConjugatedKnownSourceCurves
import AJY4SameCopiedSourceFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularPhysicalFourier
open Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.BoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularSmoothSources Grad.AnnularStrongOrbit
open Grad.SourceCollarFullSource Grad.SourceCollarAngular

/-- The SAME physical finite source has phase-conjugated radial Hilbert
curves at every original inserted grade, smooth up to both collar endpoints. -/
theorem finiteSourcePhysicalField_conjugated_radial (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) {field : DivisionRow 1 lower}
    (source : FiniteSmoothStoredRow lower field) :
    ∃ curve : ℕ → ℝ → CellL2 1,
      (∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)) ∧
      (∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
        curve grade radius mode =
          ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
            ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
              angularCoefficient (fun axial => angularCoefficient
                (fun polar => finiteSourcePhysicalField parameters lower bounded source
                  (radius, polar, axial)) mode.1) mode.2)) := by
  refine ⟨source.conjugatedPolynomial, source.conjugatedPolynomial_smooth positive, ?_⟩
  intro grade radius inside mode
  rw [finiteSourcePhysicalField_coefficient parameters lower positive bounded source radius inside mode,
    source.conjugatedPolynomial_grade, source.conjugatedPolynomial_physical parameters 0]
  norm_cast

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : OriginalSmoothSourceCore parameters)

theorem originalSmoothSourcePhysicalF0_conjugated_radial :
    ∃ curve : ℕ → ℝ → CellL2 1,
      (∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)) ∧
      (∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
        curve grade radius mode =
          ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
            ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
              angularCoefficient (fun axial => angularCoefficient
                (fun polar => originalSmoothSourcePhysicalF0 parameters lower positive bounded core
                  (radius, polar, axial)) mode.1) mode.2)) :=
  finiteSourcePhysicalField_conjugated_radial parameters lower positive bounded
    ((originalSmoothF0Row parameters lower positive bounded.le core).highWeight positive bounded.le)

theorem originalSmoothSourcePhysicalF2_conjugated_radial :
    ∃ curve : ℕ → ℝ → CellL2 1,
      (∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)) ∧
      (∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
        curve grade radius mode =
          ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
            ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
              angularCoefficient (fun axial => angularCoefficient
                (fun polar => originalSmoothSourcePhysicalF2 parameters lower positive bounded core
                  (radius, polar, axial)) mode.1) mode.2)) :=
  finiteSourcePhysicalField_conjugated_radial parameters lower positive bounded
    ((originalSmoothF2Row parameters lower positive bounded.le core).highWeight positive bounded.le)

end Grad.AnnularPhysicalFourier
