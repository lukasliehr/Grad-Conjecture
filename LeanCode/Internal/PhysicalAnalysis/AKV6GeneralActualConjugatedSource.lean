import AKV5ActualSourceCurveContract

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.SourceCollarCoefficients
open Grad.AnnularSmoothSources Grad.AnnularStrongOrbit Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.AnnularReconstruction Grad.AnnularSmoothCore

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)

/-- Literal prescribed-source physical RHS, including the full known rows and positive Rg. -/
def generalOriginalSourceRHS (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 × ComplexEuclidean 1 :=
  let row := fun index : Fin 3 => lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state index
      (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data))) radius mode
  rawOriginalSourceRHS length radius mode (row 0) (row 1) (row 2)
    (lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 3) radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive
      (strongToLow parameters lower positive bounded.le 0 0 data).ofLp.1.ofLp.2 radius mode)

/-- The SAME full inhomogeneous source in original phase-conjugated
Hilbert coordinates, with known j/c/rV and independent f and positive Rg. -/
def generalConjugatedSystemSource (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  let row := fun index : Fin 3 => generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves index (grade + 1) radius
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  ((-((length : ℂ)⁻¹)) • axial (row 1) - (radius : ℂ)⁻¹ • angular (row 2) +
    (radius : ℂ)⁻¹ • angular (curves.third (grade + 1) radius),
    hilbertMeanFree parameters (drop (row 0) + curves.force grade radius))

theorem generalConjugatedSystemSource_coefficient (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves index (grade + 1) radius mode
    let g3 := curves.third (grade + 1) radius mode
    let f := curves.force grade radius mode
    ((generalConjugatedSystemSource parameters length compact lower positive bounded state data curves grade radius).1 mode,
      (generalConjugatedSystemSource parameters length compact lower positive bounded state data curves grade radius).2 mode) =
    ((-((length : ℂ)⁻¹)) • (frequencyRatioSymbol (some true) mode • row 1) -
      (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2) +
      (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • g3),
      (if mode.1 = 0 then (0 : ℂ) else 1) • (frequencyRatioSymbol none mode • row 0 + f)) := rfl

theorem generalConjugatedSystemSource_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      ((generalConjugatedSystemSource parameters length compact lower positive bounded state data curves grade radius).1 mode,
        (generalConjugatedSystemSource parameters length compact lower positive bounded state data curves grade radius).2 mode) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          generalOriginalSourceRHS parameters length compact lower positive bounded state data radius mode) := by
  have actual := conjugatedSourceFrequency_ae parameters length lower positive grade
    (fun index radius mode => generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves index (grade + 1) radius mode)
    (fun index radius mode => lowRhoPhysicalCoefficient parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state index
        (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
          data))) radius mode)
    (fun radius mode => curves.force grade radius mode)
    (fun radius mode => curves.third (grade + 1) radius mode)
    (fun radius mode => lowRhoPhysicalCoefficient parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        data 3) radius mode)
    (fun radius mode => lowRhoPhysicalCoefficient parameters lower positive
      ((strongToLow parameters lower positive bounded.le 0 0
        data).ofLp.1.ofLp.2) radius mode)
    (fun index => generalConjugatedKnownRowCurve_actual parameters length compact lower positive bounded state data curves index (grade + 1))
    (by simpa only [Complex.ofReal_pow, Grad.SourceCollarDivision.annularFrequency, Grad.AnnularVariational.annularFrequency] using curves.forceSame grade)
    (by simpa only [Complex.ofReal_pow, Grad.SourceCollarDivision.annularFrequency, Grad.AnnularVariational.annularFrequency] using curves.thirdSame (grade+1))
  filter_upwards [actual] with radius same
  intro mode
  exact (generalConjugatedSystemSource_coefficient parameters length compact lower positive bounded state data curves grade radius mode).trans (same mode)

/-- The actual original kernel theorem gives full source smoothness from
the prescribed source representatives, at the unchanged analytic width. -/
theorem generalConjugatedSystemSource_smooth (grade : ℕ)
    :
    ContDiffOn ℝ ∞ (generalConjugatedSystemSource parameters length compact lower positive bounded state data curves grade)
      (Icc lower 1) := by
  have rowsSmooth (index : Fin 3) := generalConjugatedKnownRowCurve_smooth parameters length compact lower positive bounded state data curves index (grade+1)
  let row := fun index : Fin 3 => generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves index (grade + 1)
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  have cSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => axial (row 1 radius)) (Icc lower 1) :=
    (axial.restrictScalars ℝ).contDiff.comp_contDiffOn (rowsSmooth 1)
  have vSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => angular (row 2 radius)) (Icc lower 1) :=
    (angular.restrictScalars ℝ).contDiff.comp_contDiffOn (rowsSmooth 2)
  have gSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => angular
      (curves.third (grade + 1) radius)) (Icc lower 1) :=
    (angular.restrictScalars ℝ).contDiff.comp_contDiffOn
      (curves.thirdSmooth (grade + 1))
  have xSmooth := ((cSmooth.const_smul (-((length : ℂ)⁻¹))).sub
    ((reciprocalRadius_smooth lower positive).smul vSmooth)).add ((reciprocalRadius_smooth lower positive).smul gSmooth)
  have xiSmooth := ((hilbertMeanFree parameters).restrictScalars ℝ).contDiff.comp_contDiffOn
    (((drop.restrictScalars ℝ).contDiff.comp_contDiffOn (rowsSmooth 0)).add
      (curves.forceSmooth grade))
  exact xSmooth.prodMk xiSmooth

end Grad.AnnularGeneralSourceRegularity
