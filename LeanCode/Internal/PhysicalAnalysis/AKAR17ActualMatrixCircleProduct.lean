import AKAR13LiteralOriginalCircleCoefficients
import AKAC25SameMatrixPointwiseAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryKernelAction Grad.ActualSmoothPhysicalField Grad.ActualPhysicalField Grad.AnnularReconstruction

def OriginalCircleRepresents {dimension : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (field : CellL2 dimension) (source : ℝ × ℝ → ComplexEuclidean dimension) : Prop :=
  ∀ mode, lambdaCircleCoefficient parameters radius.val field mode = doubleCoefficient source mode

/-- Reuse the accepted literal physical matrix convolution to identify the
new original Wλ circle action on the same source. -/
theorem OriginalCircleRepresents.matrix {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (radius : RadialPoint)
    (field : CellL2 input) (source : ℝ × ℝ → ComplexEuclidean input) (continuousSource : Continuous source)
    (represented : OriginalCircleRepresents parameters radius field source) :
    OriginalCircleRepresents parameters radius (originalCircleFamilyAction parameters family coherent radius field)
      (physicalMatrixProduct parameters family radius.val radius.property.1 radius.property.2 source) := by
  intro mode
  have actual := physicalMatrixProduct_hasSum parameters family coherent radius.val radius.property.1 radius.property.2
    source continuousSource mode
  have weighted := lambdaCircleAction_original_coefficient parameters radius
    (originalMatrixRadialKernel parameters family coherent radius) field mode
  apply weighted.unique
  apply actual.congr_fun
  intro shift
  rw [represented]
  rfl

theorem OriginalCircleRepresents.matrix_literal {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (radius : RadialPoint)
    (field : CellL2 input) (source : ℝ × ℝ → ComplexEuclidean input) (continuousSource : Continuous source)
    (represented : OriginalCircleRepresents parameters radius field source) (mode : ℤ × ℤ) :
    lambdaCircleCoefficient parameters radius.val (originalCircleFamilyAction parameters family coherent radius field) mode =
      doubleCoefficient (fun angles => WithLp.toLp 2
        ((familyMatrix family 0 angles.2 (polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)).mulVec (source angles))) mode := by
  have result := represented.matrix parameters family coherent radius field source continuousSource mode
  have equality : physicalMatrixProduct parameters family radius.val radius.property.1 radius.property.2 source =
      (fun angles => WithLp.toLp 2 ((familyMatrix family 0 angles.2 (polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)).mulVec (source angles))) := by
    funext angles
    exact physicalMatrixProduct_apply parameters family radius.val radius.property.1 radius.property.2 source angles
  exact result.trans (congrArg (fun function => doubleCoefficient function mode) equality)

end Grad.OriginalKernelRetainedDecay
