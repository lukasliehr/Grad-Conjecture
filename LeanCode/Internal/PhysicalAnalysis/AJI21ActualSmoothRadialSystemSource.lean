import AJI20ActualUnknownInputCoefficients
import AJL7SameKnownPhysicalResponseCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularRadialSmoothness Grad.AnnularReconstruction
open Grad.AnnularStrongOrbit Grad.AnnularSmoothSources

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (core : OriginalSmoothSourceCore parameters)

/-- The original inhomogeneous radial system, including source contributions
inside j/c/rV and independent f and r*g, all from the same source core. -/
def originalRadialSystemSource (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  let row := fun index : Fin 3 => smoothKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core index (grade + 1) radius
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  ((-((length : ℂ)⁻¹)) • axial (row 1) - (radius : ℂ)⁻¹ • angular (row 2) +
    (radius : ℂ)⁻¹ • angular (smoothG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius),
    hilbertMeanFree parameters (drop (row 0) + smoothF1SourceCurve parameters lower length positive bounded.le lengthPositive core grade radius))

theorem originalRadialSystemSource_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade) (Icc lower 1) := by
  let row := fun index : Fin 3 => smoothKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core index (grade + 1)
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  have rowSmooth (index : Fin 3) : ContDiffOn ℝ ∞ (row index) (Icc lower 1) :=
    smoothKnownPhysicalRowCurve_smooth parameters length compact lower positive bounded lengthPositive state core index (grade + 1)
  have cSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => axial (row 1 radius)) (Icc lower 1) :=
    (axial.restrictScalars ℝ).contDiff.comp_contDiffOn (rowSmooth 1)
  have vSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => angular (row 2 radius)) (Icc lower 1) :=
    (angular.restrictScalars ℝ).contDiff.comp_contDiffOn (rowSmooth 2)
  have gSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => angular
      (smoothG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius)) (Icc lower 1) :=
    (angular.restrictScalars ℝ).contDiff.comp_contDiffOn
      (smoothG3SourceCurve_smooth parameters lower length positive bounded.le lengthPositive core (grade + 1))
  have xSmooth := ((cSmooth.const_smul (-((length : ℂ)⁻¹))).sub
    ((reciprocalRadius_smooth lower positive).smul vSmooth)).add ((reciprocalRadius_smooth lower positive).smul gSmooth)
  have xiSmooth := ((hilbertMeanFree parameters).restrictScalars ℝ).contDiff.comp_contDiffOn
    (((drop.restrictScalars ℝ).contDiff.comp_contDiffOn (rowSmooth 0)).add
      (smoothF1SourceCurve_smooth parameters lower length positive bounded.le lengthPositive core grade))
  exact xSmooth.prodMk xiSmooth

end Grad.AnnularSmoothCore
