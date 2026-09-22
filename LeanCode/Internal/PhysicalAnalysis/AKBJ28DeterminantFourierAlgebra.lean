import AKBJ19NativeDerivativeSections
import AKBJ24ScalarProjectionFourierAndPolar
import AKAM2ActualSignedDeterminantFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualScalarWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarDivision Grad.ActualCartesianFlux
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianDescent Grad.ActualDeterminantEquations
open Grad.ActualCartesianWeakEquations Grad.RepresentedKernel.SpatialProduct

private theorem scalarAngularCoefficient_smul (scalar : ℂ) (field : ℝ → ℂ) (cell : ℤ) :
    angularCoefficient (fun axial => scalar • field axial) cell = scalar • angularCoefficient field cell := by
  simp only [angularCoefficient_compact_general]
  have integrands : (fun angle => cellExponential (-cell) angle • (scalar • field angle)) =
      fun angle => scalar • (cellExponential (-cell) angle • field angle) :=
    funext (fun angle => smul_comm _ _ _)
  rw [integrands,integral_smul]
  exact smul_comm _ _ _

def determinantRowValue (length : ℝ) (first second third : ComplexEuclidean 3) : ℂ :=
  (length : ℂ) * (first 0 + second 1) + third 2

theorem determinantRowValue_axialCell (length : ℝ) (first second third : ℝ → ComplexEuclidean 3)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (thirdContinuous : Continuous third)
    (cell : ℤ) :
    angularCoefficient (fun axial => determinantRowValue length (first axial) (second axial) (third axial)) cell =
      determinantRowValue length (angularCoefficient first cell) (angularCoefficient second cell) (angularCoefficient third cell) := by
  have componentContinuous (field : ℝ → ComplexEuclidean 3) (continuousField : Continuous field) (coordinate : Fin 3) :
      Continuous (fun axial => field axial coordinate) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) coordinate).continuous.comp continuousField
  have addition := angularCoefficient_add_general (fun axial => (length : ℂ) * (first axial 0 + second axial 1))
    (fun axial => third axial 2) ((componentContinuous first firstContinuous 0).add (componentContinuous second secondContinuous 1) |>.const_mul _)
    (componentContinuous third thirdContinuous 2) cell
  have scalar := scalarAngularCoefficient_smul (length : ℂ) (fun axial => first axial 0 + second axial 1) cell
  have innerAddition := angularCoefficient_add_general (fun axial => first axial 0) (fun axial => second axial 1)
    (componentContinuous first firstContinuous 0) (componentContinuous second secondContinuous 1) cell
  have firstSame := (angularCoefficient_component first firstContinuous 0 cell).symm
  have secondSame := (angularCoefficient_component second secondContinuous 1 cell).symm
  have thirdSame := (angularCoefficient_component third thirdContinuous 2 cell).symm
  change angularCoefficient (fun axial => (length : ℂ) * (first axial 0 + second axial 1) + third axial 2) cell = _
  rw [addition]
  change angularCoefficient (fun axial => (length : ℂ) • (first axial 0 + second axial 1)) cell + _ = _
  rw [scalar,innerAddition,firstSame,secondSame,thirdSame]
  rfl

theorem nativeLocalField_axialPeriodic {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ}
    {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1) (point : Spatial) :
    Function.Periodic (fun axial => curves.cartesianField bounded (point,axial)) (2*Real.pi) := by
  intro axial
  exact curves.fullField_cell_periodic bounded _ _ axial

/-- Fixed L,L,1 column normalization commutes with genuine spatial differentiation. -/
theorem determinantFluxProjection_fderiv (length : ℝ) (coordinate : Fin 3)
    (field : Spatial → ComplexEuclidean 3) (point : Spatial) (differentiable : DifferentiableAt ℝ field point)
    (direction : Spatial) :
    fderiv ℝ (fun query => determinantFluxProjection length coordinate (field query)) point direction =
      determinantFluxProjection length coordinate (fderiv ℝ field point direction) := by
  have derivative := (determinantFluxProjection length coordinate).hasFDerivAt.comp point differentiable.hasFDerivAt
  exact congrArg (fun map : Spatial →L[ℝ] ℂ => map direction) derivative.fderiv

end Grad.ActualScalarWeakEquations
