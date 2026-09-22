import AJQ1OriginalSourceFrequencyAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularSmoothSources Grad.AnnularStrongOrbit
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCurrentLow Grad.AnnularKnownLow

/-- AE assembly is independent of the concrete full source carrier. -/
theorem sourceFrequency_ae (length lower : ℝ) (positive : 0 < lower) (grade : ℕ)
    (row raw : Fin 3 → ℝ → (ℤ × ℤ) → ComplexEuclidean 1)
    (f g3 rawF rawG : ℝ → (ℤ × ℤ) → ComplexEuclidean 1)
    (rowSame : ∀ index, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      row index radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 1) • raw index radius mode)
    (fSame : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      f radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ grade • rawF radius mode)
    (gSame : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      g3 radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 1) • (radius • rawG radius mode)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      ((-((length : ℂ)⁻¹)) • (frequencyRatioSymbol (some true) mode • row 1 radius mode) -
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2 radius mode) +
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • g3 radius mode),
        (if mode.1 = 0 then (0 : ℂ) else 1) •
          (frequencyRatioSymbol none mode • row 0 radius mode + f radius mode)) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        rawOriginalSourceRHS length radius mode (raw 0 radius mode) (raw 1 radius mode)
          (raw 2 radius mode) (rawF radius mode) (rawG radius mode) := by
  filter_upwards [rowSame 0, rowSame 1, rowSame 2, fSame, gSame,
    ae_restrict_mem measurableSet_Icc] with radius sameJ sameC sameV sameF sameG inside
  intro mode
  rw [sameJ mode, sameC mode, sameV mode, sameF mode, sameG mode]
  simpa only [Complex.ofReal_pow, Grad.SourceCollarDivision.annularFrequency,
      Grad.AnnularVariational.annularFrequency] using
    originalSource_frequency_algebra length radius (positive.trans_le inside.1).ne' mode grade
      (raw 0 radius mode) (raw 1 radius mode) (raw 2 radius mode) (rawF radius mode) (rawG radius mode)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (core : OriginalSmoothSourceCore parameters)

/-- Original j/c/rV acting on the once-only known F0/RF0/F2 packet, and
independent original f and g, in the unchanged AJG9 physical decoding. -/
def actualOriginalSourceRHS (radius : ℝ) (mode : ℤ × ℤ) :
    ComplexEuclidean 1 × ComplexEuclidean 1 :=
  let data := (strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core
  let bulk := strongKnownBulk parameters lower positive bounded.le data
  let row := fun index : Fin 3 => lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state index
      (knownLowSevenPacket lower bulk)) radius mode
  rawOriginalSourceRHS length radius mode (row 0) (row 1) (row 2)
    (lowRhoPhysicalCoefficient parameters lower positive (bulk 3) radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive
      ((strongToLow parameters lower positive bounded.le 0 0 data).ofLp.1.ofLp.2) radius mode)

/-- The Hilbert operator formula evaluated at one Fourier mode. -/
theorem originalRadialSystemSource_coefficient (grade : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => smoothKnownPhysicalRowCurve parameters length compact lower
      positive bounded lengthPositive state core index (grade + 1) radius mode
    let g3 := smoothG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius mode
    let f := smoothF1SourceCurve parameters lower length positive bounded.le lengthPositive core grade radius mode
    ((originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).1 mode,
      (originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).2 mode) =
    ((-((length : ℂ)⁻¹)) • (frequencyRatioSymbol (some true) mode • row 1) -
      (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2) +
      (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • g3),
      (if mode.1 = 0 then (0 : ℂ) else 1) • (frequencyRatioSymbol none mode • row 0 + f)) := rfl

/-- Every polynomial-grade source curve has the exact original physical RHS.
No regularity of the solution is assumed; this concerns the SAME smooth source. -/
theorem originalRadialSystemSource_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      ((originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).1 mode,
        (originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius).2 mode) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        actualOriginalSourceRHS parameters length compact lower positive bounded lengthPositive state core radius mode := by
  have actual := sourceFrequency_ae length lower positive grade
    (fun index radius mode => smoothKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core index (grade + 1) radius mode)
    (fun index radius mode => lowRhoPhysicalCoefficient parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state index
        (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
          ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)))) radius mode)
    (fun radius mode => smoothF1SourceCurve parameters lower length positive bounded.le lengthPositive core grade radius mode)
    (fun radius mode => smoothG3SourceCurve parameters lower length positive bounded.le lengthPositive core (grade + 1) radius mode)
    (fun radius mode => lowRhoPhysicalCoefficient parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core) 3) radius mode)
    (fun radius mode => lowRhoPhysicalCoefficient parameters lower positive
      ((strongToLow parameters lower positive bounded.le 0 0
        ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)).ofLp.1.ofLp.2) radius mode)
    (fun index => smoothKnownPhysicalRowCurve_actual parameters length compact lower positive bounded lengthPositive state core index (grade + 1))
    (smoothF1SourceCurve_actual parameters lower length positive bounded.le lengthPositive core grade)
    (smoothG3SourceCurve_actual parameters lower length positive bounded.le lengthPositive core (grade + 1))
  filter_upwards [actual] with radius same
  intro mode
  exact (originalRadialSystemSource_coefficient parameters length compact lower positive bounded lengthPositive state core grade radius mode).trans (same mode)

end Grad.AnnularSmoothCore
