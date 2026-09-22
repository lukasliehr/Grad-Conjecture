import AJI27ActualUnknownRadialRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace

/-- Assembly of the exact physical unknown RHS from its coefficient laws.
The concrete row providers are AJI26 and the SAME field grades are AJI17. -/
theorem unknownFrequency_ae (length lower : ℝ) (grade : ℕ)
    (row raw : Fin 3 → ℝ → (ℤ × ℤ) → ComplexEuclidean 1)
    (x rawX : ℝ → (ℤ × ℤ) → ComplexEuclidean 1)
    (rowSame : ∀ index, ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      row index radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 1) • raw index radius mode)
    (xSame : ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      x radius mode = (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 2) • rawX radius mode) :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      ((-((radius : ℂ)⁻¹)) • (frequencyRatioSymbol none mode • (frequencyRatioSymbol none mode • x radius mode)) -
        (length : ℂ)⁻¹ • (frequencyRatioSymbol (some true) mode • row 1 radius mode) -
        (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2 radius mode),
        (if mode.1 = 0 then (0 : ℂ) else 1) • (frequencyRatioSymbol none mode • row 0 radius mode)) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        rawOriginalUnknownRHS length radius mode (rawX radius mode)
          (raw 0 radius mode) (raw 1 radius mode) (raw 2 radius mode) := by
  filter_upwards [rowSame 0, rowSame 1, rowSame 2, xSame] with radius sameJ sameC sameV sameX
  intro mode
  rw [sameJ mode, sameC mode, sameV mode, sameX mode]
  simpa only [Complex.ofReal_pow, Grad.SourceCollarDivision.annularFrequency,
    Grad.AnnularVariational.annularFrequency] using
    originalUnknown_frequency_algebra length radius mode grade
      (rawX radius mode) (raw 0 radius mode) (raw 1 radius mode) (raw 2 radius mode)

end Grad.AnnularSmoothCore
