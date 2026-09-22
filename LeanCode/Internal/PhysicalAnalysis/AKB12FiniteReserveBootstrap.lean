import AKB11SameConjugatedResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace Grad.AnnularWeightedSmoothCore
open Grad.AnnularSmoothCore

/-- Finite radial order may use its own higher Fourier input grade. The
induction keeps ALL grades of the SAME field, so no analytic width is lost. -/
theorem finiteReservePairScale_smooth
    (lower : ℝ) (bounded : lower < 1)
    (field source : ℕ → ℝ → PhysicalHilbertPair)
    (inputGrade : ℕ → ℕ → ℕ)
    (operator : ℕ → ℕ → ℝ → PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair)
    (continuous : ∀ grade, ContinuousOn (field grade) (Icc lower 1))
    (sourceSmooth : ∀ grade, ContDiffOn ℝ ∞ (source grade) (Icc lower 1))
    (operatorSmooth : ∀ order grade, ContDiffOn ℝ (order : ℕ) (operator order grade) (Icc lower 1))
    (xLaw : ∀ order grade mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun point => (field grade point).1 mode)
        (((operator order grade radius) (field (inputGrade order grade) radius) + source grade radius).1 mode)
        (Icc lower 1) radius)
    (xiLaw : ∀ order grade mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun point => (field grade point).2 mode)
        (((operator order grade radius) (field (inputGrade order grade) radius) + source grade radius).2 mode)
        (Icc lower 1) radius) :
    ∀ grade, ContDiffOn ℝ ∞ (field grade) (Icc lower 1) := by
  have orders (order : ℕ) : ∀ grade, ContDiffOn ℝ order (field grade) (Icc lower 1) := by
    induction order with
    | zero => exact fun grade => contDiffOn_zero.mpr (continuous grade)
    | succ order previous =>
      intro grade
      let rhs : ℝ → PhysicalHilbertPair := fun radius =>
        (operator order grade radius) (field (inputGrade order grade) radius) + source grade radius
      have action := ((ContinuousLinearMap.apply ℂ PhysicalHilbertPair).flip.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        (operatorSmooth order grade) (previous (inputGrade order grade))
      have rhsSmooth : ContDiffOn ℝ order rhs (Icc lower 1) :=
        action.add ((contDiffOn_infty.mp (sourceSmooth grade)) order)
      have law (radius : ℝ) (inside : radius ∈ Icc lower 1) :
          HasDerivWithinAt (field grade) (rhs radius) (Icc lower 1) radius :=
        hilbertPairDerivative_of_coordinates lower bounded.le (field grade) rhs (continuous grade)
          rhsSmooth.continuousOn (xLaw order grade) (xiLaw order grade) radius inside
      exact closedCollar_succ lower bounded order (field grade) rhs law rhsSmooth
  exact fun grade => contDiffOn_infty.mpr (fun order => orders order grade)

end Grad.AnnularWeightedSmoothCore
