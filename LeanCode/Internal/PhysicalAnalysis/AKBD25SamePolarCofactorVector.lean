import AKBD24GenuineCartesianDeterminantDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.BoundaryTrace
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Ledger Grad.ActualPolarFlux

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Assemble the three already constructed actual cofactor-row fields;
this uses only the existing exact finite coordinate inclusions. -/
def samePolarCofactorVector :=
  (((polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0).bulkUnit (0 : Fin 3) 0).add
    ((polarCofactorFluxCurves parameters length compact lower positive bounded state curves 1).bulkUnit (1 : Fin 3) 0)).add
    ((polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2).bulkUnit (2 : Fin 3) 0)

theorem samePolarCofactorVector_component (component : Fin 3) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (samePolarCofactorVector parameters length compact lower positive bounded state curves).fullField bounded (radius,angles) component =
      (polarCofactorFluxCurves parameters length compact lower positive bounded state curves component).fullField bounded (radius,angles) 0 := by
  unfold samePolarCofactorVector
  rw [SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_add _ bounded _ radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded (0 : Fin 3) 0 radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded (1 : Fin 3) 0 radius inside angles,
    SmoothLowPhysicalRow.fullField_bulkUnit _ bounded (2 : Fin 3) 0 radius inside angles]
  fin_cases component <;> simp [matrixUnit_apply,operatorBasis]

theorem samePolarCofactorVector_directional (component : Fin 3) (direction : ℝ × (ℝ × ℝ))
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ) :
    scalarDirectionalField (samePolarCofactorVector parameters length compact lower positive bounded state curves) bounded component direction (radius,angles) =
      scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves component) bounded 0 direction (radius,angles) := by
  let vector := samePolarCofactorVector parameters length compact lower positive bounded state curves
  let scalar := polarCofactorFluxCurves parameters length compact lower positive bounded state curves component
  have same : (fun query => vector.fullField bounded query component) =ᶠ[𝓝 (radius,angles)]
      (fun query => scalar.fullField bounded query 0) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds (x := (radius,angles)) ⟨inside,mem_univ _⟩] with query member
    exact samePolarCofactorVector_component parameters length compact lower positive bounded state curves component query.1 ⟨member.1.1.le,member.1.2.le⟩ query.2
  have actual := (fullScalarField_hasFDerivAt scalar bounded 0 (radius,angles) inside).congr_of_eventuallyEq same
  exact congrArg (fun derivative : (ℝ × (ℝ × ℝ)) →L[ℝ] ℂ => derivative direction)
    ((fullScalarField_hasFDerivAt vector bounded component (radius,angles) inside).unique actual)

end Grad.ActualDeterminantEquations
