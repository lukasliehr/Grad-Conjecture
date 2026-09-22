import AKD7ExactConjugatedSourceFrequencyAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.SourceCollarCoefficients
open Grad.AnnularSmoothSources Grad.AnnularStrongOrbit Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.AnnularReconstruction

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (core : OriginalSmoothSourceCore parameters)

/-- The SAME full inhomogeneous source in original phase-conjugated
Hilbert coordinates, with known j/c/rV and independent f and positive Rg. -/
def conjugatedRadialSystemSource (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  let row := fun index : Fin 3 => conjugatedKnownPhysicalRowCurve parameters length compact lower
    positive bounded lengthPositive state core index (grade + 1) radius
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  ((-((length : ℂ)⁻¹)) • axial (row 1) - (radius : ℂ)⁻¹ • angular (row 2) +
    (radius : ℂ)⁻¹ • angular (conjugatedG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius),
    hilbertMeanFree parameters (drop (row 0) + conjugatedKnownRowCurve parameters lower length positive bounded.le lengthPositive core 3 grade radius))

theorem conjugatedRadialSystemSource_coefficient (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => conjugatedKnownPhysicalRowCurve parameters length compact lower
      positive bounded lengthPositive state core index (grade + 1) radius mode
    let g3 := conjugatedG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius mode
    let f := conjugatedKnownRowCurve parameters lower length positive bounded.le lengthPositive core 3 grade radius mode
    ((conjugatedRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).1 mode,
      (conjugatedRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).2 mode) =
    ((-((length : ℂ)⁻¹)) • (frequencyRatioSymbol (some true) mode • row 1) -
      (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2) +
      (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • g3),
      (if mode.1 = 0 then (0 : ℂ) else 1) • (frequencyRatioSymbol none mode • row 0 + f)) := rfl

theorem conjugatedRadialSystemSource_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      ((conjugatedRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).1 mode,
        (conjugatedRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).2 mode) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          actualOriginalSourceRHS parameters length compact lower positive bounded lengthPositive state core radius mode) := by
  have actual := conjugatedSourceFrequency_ae parameters length lower positive grade
    (fun index radius mode => conjugatedKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core index (grade + 1) radius mode)
    (fun index radius mode => lowRhoPhysicalCoefficient parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state index
        (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
          ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)))) radius mode)
    (fun radius mode => conjugatedKnownRowCurve parameters lower length positive bounded.le lengthPositive core 3 grade radius mode)
    (fun radius mode => conjugatedG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius mode)
    (fun radius mode => lowRhoPhysicalCoefficient parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core) 3) radius mode)
    (fun radius mode => lowRhoPhysicalCoefficient parameters lower positive
      ((strongToLow parameters lower positive bounded.le 0 0
        ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)).ofLp.1.ofLp.2) radius mode)
    (fun index => conjugatedKnownPhysicalRowCurve_actual parameters length compact lower positive bounded lengthPositive state core index (grade + 1))
    (conjugatedKnownRowCurve_actual parameters lower length positive bounded.le lengthPositive core 3 grade)
    (conjugatedG3SourceCurve_actual parameters lower length positive bounded.le lengthPositive core (grade + 1))
  filter_upwards [actual] with radius same
  intro mode
  exact (conjugatedRadialSystemSource_coefficient parameters length compact lower positive bounded lengthPositive state core grade radius mode).trans (same mode)

/-- Pure assembly preserves smoothness once the actual three row curves
have been proved smooth; independent f and r*g are already unconditional. -/
theorem conjugatedRadialSystemSource_smooth_of_rows (grade : ℕ)
    (rowsSmooth : ∀ index : Fin 3, ContDiffOn ℝ ∞
      (conjugatedKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core index (grade + 1))
      (Icc lower 1)) :
    ContDiffOn ℝ ∞ (conjugatedRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade)
      (Icc lower 1) := by
  let row := fun index : Fin 3 => conjugatedKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core index (grade + 1)
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  have cSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => axial (row 1 radius)) (Icc lower 1) :=
    (axial.restrictScalars ℝ).contDiff.comp_contDiffOn (rowsSmooth 1)
  have vSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => angular (row 2 radius)) (Icc lower 1) :=
    (angular.restrictScalars ℝ).contDiff.comp_contDiffOn (rowsSmooth 2)
  have gSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => angular
      (conjugatedG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius)) (Icc lower 1) :=
    (angular.restrictScalars ℝ).contDiff.comp_contDiffOn
      (conjugatedG3SourceCurve_smooth parameters lower length positive bounded.le lengthPositive core (grade + 1))
  have xSmooth := ((cSmooth.const_smul (-((length : ℂ)⁻¹))).sub
    ((reciprocalRadius_smooth lower positive).smul vSmooth)).add ((reciprocalRadius_smooth lower positive).smul gSmooth)
  have xiSmooth := ((hilbertMeanFree parameters).restrictScalars ℝ).contDiff.comp_contDiffOn
    (((drop.restrictScalars ℝ).contDiff.comp_contDiffOn (rowsSmooth 0)).add
      (conjugatedKnownRowCurve_smooth parameters lower length positive bounded.le lengthPositive core 3 grade))
  exact xSmooth.prodMk xiSmooth

end Grad.AnnularSmoothCore
