import AAZJ13OriginalTwoTorusReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularRegularity

/-- Concrete properties of the same physical Fourier series. The record
contains no new field coordinates: every clause refers to the actual series,
its literal derivatives, or the actual double Fourier integrals. -/
structure AnnularJointPhysicalRealization (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order)) : Prop where
  smooth : ∀ radial angular cell, ContDiffOn ℝ ∞
    (annularMixedFourierField parameters lower positive bounded jet weak radial angular cell) (annularJointInterior lower)
  closedContinuous : ∀ radial angular cell,
    Continuous (fun point : (Icc lower (1 : ℝ)) × (CellCircle × CellCircle) =>
      annularMixedTorusSection parameters lower positive bounded jet weak radial angular cell point.2 point.1)
  radialDerivative : ∀ radial angular cell angles radius (inside : radius ∈ Icc lower 1),
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
      (annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell angles))
      (annularMixedFourierSection parameters lower positive bounded jet weak (radial + 1) angular cell angles ⟨radius, inside⟩)
      (Icc lower 1) radius
  angularDerivative : ∀ radial angular cell polar axial,
    HasDerivAt (fun angle => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (angle, axial))
      (annularMixedFourierSection parameters lower positive bounded jet weak radial (angular + 1) cell (polar, axial)) polar
  cellDerivative : ∀ radial angular cell polar axial,
    HasDerivAt (fun angle => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (polar, angle))
      (annularMixedFourierSection parameters lower positive bounded jet weak radial angular (cell + 1) (polar, axial)) axial
  coefficient : ∀ radial angular cell (radius : Icc lower (1 : ℝ)) (query : HighAnnularMode),
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => annularMixedFourierSection parameters lower positive bounded jet weak radial angular cell (polar, axial) radius)
      query.val.1) query.val.2 = annularMixedSymbol angular cell query •
        annularPhysicalJetSection parameters lower positive bounded jet weak radial query radius
  originalBulk : ∀ radial query,
    radialSectionL2 1 lower positive bounded.le
      (annularReconstructedCoefficientSection parameters lower positive bounded jet weak grades radial query) =
      annularDecodeMode parameters lower positive query (jet radial query)

/-- Construction from genuine physical weak jets and their proved original
weighted grades; there is no hypothesis of joint smoothness. -/
theorem annularPhysicalJets_jointRealization (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order)) :
    AnnularJointPhysicalRealization parameters lower positive bounded jet weak grades where
  smooth := annularMixedFourierField_smooth parameters lower positive bounded jet weak grades
  closedContinuous := annularMixedTorusValue_continuous parameters lower positive bounded jet weak grades
  radialDerivative := annularMixedFourierSection_radialDerivative parameters lower positive bounded jet weak grades
  angularDerivative := annularMixedFourierSection_angular parameters lower positive bounded jet weak grades
  cellDerivative := annularMixedFourierSection_cell parameters lower positive bounded jet weak grades
  coefficient := annularMixedFourierSection_coefficient parameters lower positive bounded jet weak grades
  originalBulk := annularReconstructedCoefficientSection_bulk parameters lower positive bounded jet weak grades

end Grad.AnnularJointRegularity
