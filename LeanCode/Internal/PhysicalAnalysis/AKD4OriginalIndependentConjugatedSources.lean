import AKD3CopiedSourceConjugatedRadialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.SourceCollarCoefficients
open Grad.AnnularSourceGraph Grad.AnnularStrongOrbit Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCurrentSource Grad.AnnularCurrentLow

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (core : OriginalSmoothSourceCore parameters)

/-- The original independently prescribed strengthened G3 coordinate,
before angular decoding. Its finite radial coefficients are already genuine. -/
def originalSmoothStrengthenedGRow : FiniteSmoothStoredRow lower
    ((originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.2) := by
  rw [(originalSmoothStrongData_forcing parameters lower positive bounded core).2]
  exact finiteOrdinarySmoothRow 1 lower (meanFreeRadialCore core.1.2.2)

def conjugatedOriginalF1Curve (grade : ℕ) : ℝ → CellL2 1 :=
  ((originalSmoothFRow parameters lower positive bounded core).highWeight positive bounded).conjugatedPolynomial grade

def conjugatedOriginalStrengthenedGCurve (grade : ℕ) : ℝ → CellL2 1 :=
  ((originalSmoothStrengthenedGRow parameters lower positive bounded core).highWeight positive bounded).conjugatedPolynomial grade

theorem conjugatedOriginalF1Curve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (conjugatedOriginalF1Curve parameters lower positive bounded core grade) (Icc lower 1) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_smooth _ positive grade

theorem conjugatedOriginalStrengthenedGCurve_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (conjugatedOriginalStrengthenedGCurve parameters lower positive bounded core grade) (Icc lower 1) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_smooth _ positive grade

theorem conjugatedOriginalF1Curve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedOriginalF1Curve parameters lower positive bounded core grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (divisionHighWeight lower positive bounded
                (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.1) radius mode) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_actual _ parameters positive grade

theorem conjugatedOriginalStrengthenedGCurve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedOriginalStrengthenedGCurve parameters lower positive bounded core grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (divisionHighWeight lower positive bounded
                (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.2) radius mode) :=
  FiniteSmoothStoredRow.conjugatedPolynomial_actual _ parameters positive grade

theorem conjugatedOriginalF1Curve_grade (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    conjugatedOriginalF1Curve parameters lower positive bounded core grade radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
        conjugatedOriginalF1Curve parameters lower positive bounded core 0 radius mode :=
  FiniteSmoothStoredRow.conjugatedPolynomial_grade _ grade radius mode

theorem conjugatedOriginalStrengthenedGCurve_grade (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    conjugatedOriginalStrengthenedGCurve parameters lower positive bounded core grade radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
        conjugatedOriginalStrengthenedGCurve parameters lower positive bounded core 0 radius mode :=
  FiniteSmoothStoredRow.conjugatedPolynomial_grade _ grade radius mode

end Grad.AnnularSmoothSources
