import GC10Identity

noncomputable section

open Grad.GaugeCoefficients.Envelope

namespace Grad.GaugeCoefficients.Algebra

def coefficientCompositionOperation {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) :
    CompositionOperation L sigma gamma ell :=
  fun grade _ _ _ outer inner =>
    coefficientComposition admissible grade outer inner

def coefficientAlgebraConstruction (L sigma gamma ell : ℝ)
    (admissible : Admissible L sigma gamma ell) :
    Construction L sigma gamma ell where
  compose := coefficientCompositionOperation admissible
  identity := identityCoefficient L sigma gamma ell
  complete := coefficient_complete
  finiteCellCore_dense := finiteCellCore_dense
  norm_formula := coefficient_norm_formula
  weighted_derivative_literal := weighted_derivative_literal
  compose_derivative := by
    intro grade inputDimension middleDimension outputDimension outer inner cell index point
    exact coefficientComposition_derivative admissible grade outer inner cell index point
  base_product_norm := by
    intro inputDimension middleDimension outputDimension outer inner
    exact coefficientComposition_base_norm_le admissible outer inner
  graded_product_norm := by
    intro grade inputDimension middleDimension outputDimension outer inner
    exact coefficientComposition_norm_le admissible grade outer inner
  fourier_compose := by
    intro inputDimension middleDimension outputDimension outer inner angle point
    exact fourierComposition admissible outer inner angle point
  identity_goal := identityCoefficient_goal L sigma gamma ell

theorem blockGoal : BlockGoal := by
  intro L sigma gamma ell admissible
  exact ⟨coefficientAlgebraConstruction L sigma gamma ell admissible⟩

end Grad.GaugeCoefficients.Algebra
