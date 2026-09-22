import QuotientValueMap

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

/-- One signed monomial of the three-dimensional column determinant. -/
def projectionTriple (first second third : Fin 3) : ContinuousMultilinearMap ℂ
    (fun _ : Fin 3 => ComplexEuclidean 3) (ComplexEuclidean 1) :=
  ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ 3 ℂ).compContinuousLinearMap
    (fun slot => PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) (![first, second, third] slot))).smulRight
      (EuclideanSpace.single 0 1)

/-- The literal original column determinant as a fixed complex-trilinear
value map into the one-dimensional coefficient space. -/
def determinantMultilinear : ContinuousMultilinearMap ℂ
    (fun _ : Fin 3 => ComplexEuclidean 3) (ComplexEuclidean 1) :=
  projectionTriple 0 1 2 - projectionTriple 0 2 1 - projectionTriple 1 0 2 +
    projectionTriple 2 0 1 + projectionTriple 1 2 0 - projectionTriple 2 1 0

theorem determinantMultilinear_value (first second third : ComplexEuclidean 3) :
    determinantMultilinear ![first, second, third] 0 =
      Grad.NonlinearQuotient.complexDeterminant first second third := by
  rw [Grad.NonlinearQuotient.complexDeterminant_eq]
  simp [determinantMultilinear, projectionTriple,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  ring

end Grad.NonlinearQuotientBounds
