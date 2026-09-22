import GC13RadialClosure
import GC13Fixed

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

/-- All five literal coefficient operations on the frozen original-width carrier. -/
def coefficientRadialConstruction {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) : Construction L sigma gamma ell where
  admissible := admissible
  radialIntegral := coefficientRadialMap admissible
  radialIntegral_bound := coefficientRadial_bound admissible
  radialIntegral_derivative := coefficientRadial_derivative admissible
  laplacian := coefficientLaplacianMap L sigma gamma ell
  laplacian_bound := coefficientLaplacian_bound L sigma gamma ell
  laplacian_derivative := coefficientLaplacian_derivative L sigma gamma ell
  reflection := coefficientReflectionOperation L sigma gamma ell
  reflection_bound := coefficientReflection_bound L sigma gamma ell
  reflection_derivative := coefficientReflection_derivative L sigma gamma ell
  angularMean := coefficientAngularMap L sigma gamma ell
  angularMean_bound := coefficientAngular_bound L sigma gamma ell
  angularMean_value := coefficientAngular_value L sigma gamma ell
  fixedMultiplier := fun grade _inputDimension _middleDimension _outputDimension field =>
    fixedMultiplierMap admissible grade field
  fixedMultiplier_bound := fun grade _inputDimension _middleDimension _outputDimension =>
    fixedMultiplierMap_bound admissible grade
  fixedMultiplier_derivative := fun grade _inputDimension _middleDimension _outputDimension =>
    fixedMultiplierMap_derivative admissible grade

theorem blockGoal : BlockGoal := by
  intro L sigma gamma ell admissible
  exact ⟨coefficientRadialConstruction admissible⟩

end Grad.GaugeCoefficients.Radial
