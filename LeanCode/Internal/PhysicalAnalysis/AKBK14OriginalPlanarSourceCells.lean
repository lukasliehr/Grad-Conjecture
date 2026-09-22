import AKBK13OriginalProjectedCellEquation
import AKBJ5OriginalSourceCartesianCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.ActualCartesianEquations Grad.SourceCollarFullSource Grad.BoundaryTrace Grad.SourceCollar
open Grad.ActualScalarWeakEquations Grad.QuotientProjection Grad.FlatSourceProjection

theorem literalCartesianPlanarSource_planar (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angles : ℝ × ℝ) :
    planarPartMap (literalCartesianPlanarSource parameters source radius nonnegative bounded angles) =
      corePolarValue parameters (cartesianSourceVector source) radius nonnegative bounded angles := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem literalCartesianPlanarSource_continuous (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Continuous (literalCartesianPlanarSource parameters source radius nonnegative bounded) := by
  have smoothSource := corePolarValue_continuous parameters (cartesianSourceVector source) radius nonnegative bounded
  unfold literalCartesianPlanarSource
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
  apply continuous_pi
  intro coordinate
  fin_cases coordinate <;> dsimp
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 0).comp smoothSource
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) 1).comp smoothSource
  · exact continuous_const

/-- The original planar source is selected after its full axial reconstruction. -/
theorem literalCartesianPlanarSource_axialCell (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (cell : ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (polar : ℝ) :
    angularCoefficient (fun axial => planarPartMap (literalCartesianPlanarSource parameters source radius nonnegative bounded (polar,axial))) cell =
      originalCoreCell parameters (cartesianSourceVector source) cell (Grad.SourceCollarDivision.polarPlane (radius,polar)) := by
  simp_rw [literalCartesianPlanarSource_planar]
  exact originalCoreCell_polarCoefficient parameters (cartesianSourceVector source) cell radius nonnegative bounded polar

end Grad.ActualCartesianWeakEquations
