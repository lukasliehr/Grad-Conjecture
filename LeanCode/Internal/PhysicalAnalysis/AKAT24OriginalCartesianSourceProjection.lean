import AKAT23ActualSevenCartesianSources

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.QuotientProjection Grad.Constraints.Gauges Grad.FlatSourceProjection

/-- Ordinary Cartesian vector reconstruction from its literal radial and
tangential components. -/
theorem cartesianCovariantValue_polarProjections (angle : ℝ) (value : ComplexEuclidean 2) :
    cartesianCovariantValue angle (WithLp.toLp 2 ![radialProjection angle value 0,tangentialProjection angle value 0,0]) =
      WithLp.toLp 2 ![value 0,value 1,0] := by
  have circle : (Real.sin angle : ℂ)^2+(Real.cos angle : ℂ)^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  simp only [Complex.ofReal_cos,Complex.ofReal_sin] at circle
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [cartesianCovariantValue_apply,radialProjection,tangentialProjection,planarComponentMap]
  · linear_combination value 0 * circle
  · linear_combination value 1 * circle

def literalCartesianPlanarSource (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angles : ℝ × ℝ) : ComplexEuclidean 3 :=
  let value := corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded angles
  WithLp.toLp 2 ![value 0,value 1,0]

/-- The actual source has exactly the original radial Cartesian complement. -/
theorem literalCartesianPlanarSource_projected (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angles : ℝ × ℝ) :
    cartesianRadialMeanFree (literalCartesianPlanarSource parameters source radius nonnegative bounded) angles =
      cartesianCovariantValue angles.1 (WithLp.toLp 2 ![
        removePolarMean (fun query => literalPrimitiveSource parameters length source radius nonnegative bounded 0 query 0) angles,
        literalPrimitiveSource parameters length source radius nonnegative bounded 1 angles 0,0]) := by
  have original : literalCartesianPlanarSource parameters source radius nonnegative bounded =
      fun query => cartesianCovariantValue query.1 (WithLp.toLp 2 ![
        literalPrimitiveSource parameters length source radius nonnegative bounded 0 query 0,
        literalPrimitiveSource parameters length source radius nonnegative bounded 1 query 0,0]) := by
    funext query
    exact (cartesianCovariantValue_polarProjections query.1
      (corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded query)).symm
  rw [original,cartesianRadialMeanFree_polar]
  rfl

end Grad.ActualCartesianEquations
