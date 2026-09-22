import AKV18CartesianWeightedRadialSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarRestriction Grad.SourceCollarCoefficients Grad.AnnularSourceGraph
open Grad.AnnularSmoothCore

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : ACore parameters dimension)

theorem cartesianWeightedRadialCoefficient_derivative (grade order : ℕ) (mode : ℤ × ℤ) (radius : ℝ) :
    HasDerivAt (cartesianWeightedRadialCoefficient parameters field grade order mode)
      (cartesianWeightedRadialCoefficient parameters field grade (order+1) mode radius) radius := by
  unfold cartesianWeightedRadialCoefficient
  exact (radialCoefficientJet_hasDerivAt
    (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
    (originalPolarValue_smooth _) mode.1 order radius).const_smul
      ((annularFrequency mode.1 mode.2 : ℂ)^grade)

/-- Genuine derivatives in the full Fourier Hilbert norm, obtained from the
continuous next radial jet and the exact same scalar coefficient derivatives. -/
theorem cartesianWeightedRadialCurve_derivative (grade order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (cartesianWeightedRadialCurve parameters lower positive bounded field grade order)
      (cartesianWeightedRadialCurve parameters lower positive bounded field grade (order+1) radius) (Icc lower 1) radius := by
  apply hilbertDerivative_of_coordinates lower
    (cartesianWeightedRadialCurve parameters lower positive bounded field grade order)
    (cartesianWeightedRadialCurve parameters lower positive bounded field grade (order+1))
    (cartesianWeightedRadialCurve_continuous parameters lower positive bounded field grade order).continuousOn
    (cartesianWeightedRadialCurve_continuous parameters lower positive bounded field grade (order+1))
    ?_ radius inside
  intro mode point member
  rw [cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field grade (order+1) mode point member]
  exact (cartesianWeightedRadialCoefficient_derivative parameters field grade order mode point).hasDerivWithinAt.congr
    (fun query included => cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field grade order mode query included)
    (cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field grade order mode point member)

/-- The original A-core supplies every radial Hilbert derivative at every
original tangential grade, with W applied before the radial derivatives. -/
theorem cartesianWeightedRadialCurve_smooth (grade radial : ℕ) :
    ContDiffOn ℝ ∞ (cartesianWeightedRadialCurve parameters lower positive bounded field grade radial) (Icc lower 1) := by
  have orders (order : ℕ) : ∀ radial, ContDiffOn ℝ order
      (cartesianWeightedRadialCurve parameters lower positive bounded field grade radial) (Icc lower 1) := by
    induction order with
    | zero =>
      intro radial
      exact contDiffOn_zero.mpr
        (cartesianWeightedRadialCurve_continuous parameters lower positive bounded field grade radial).continuousOn
    | succ order previous =>
      intro radial
      exact closedCollar_succ lower bounded order _ _
        (cartesianWeightedRadialCurve_derivative parameters lower positive bounded field grade radial)
        (previous (radial+1))
  exact contDiffOn_infty.mpr (fun order => orders order radial)

theorem cartesianWeightedRadialCurve_shift (grade reserve radial : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    cartesianWeightedRadialCurve parameters lower positive bounded field (grade+reserve) radial radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        cartesianWeightedRadialCurve parameters lower positive bounded field grade radial radius mode := by
  rw [cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field (grade+reserve) radial mode radius inside,
    cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field grade radial mode radius inside]
  unfold cartesianWeightedRadialCoefficient
  rw [pow_add,mul_smul]
  exact smul_comm _ _ _

end Grad.AnnularGeneralSourceRegularity
