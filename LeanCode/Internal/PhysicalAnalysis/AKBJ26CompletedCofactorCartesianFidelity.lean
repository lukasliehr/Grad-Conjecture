import AKBD26SameCartesianSignedCofactorFlux
import AKAM2ActualSignedDeterminantFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.BoundaryTrace
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Ledger Grad.ActualPolarFlux
open Grad.SourceCollar Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives Grad.ActualDeterminantEquations
open Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def sameCompletedCofactorCurves :=
  (curves.covariant parameters length compact lower positive bounded state.val).cartesianCovariant.matrixAction parameters
    (originalCofactorFamily parameters length state.val.val.epsilon state.val.val.field)
    (originalCofactorFamily_estimate parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small).actualCoherent
    lower positive bounded

/-- The accepted full cofactor convolution and the accepted original determinant vector give the identical full physical field. -/
theorem sameCompletedCofactor_fullField (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (sameCompletedCofactorCurves parameters length compact lower positive bounded state small curves).fullField bounded (radius,angles) =
      (samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.fullField bounded (radius,angles) := by
  have native := (curves.covariant parameters length compact lower positive bounded state.val).cartesianCovariant.fullField_matrixAction parameters
    (originalCofactorFamily parameters length state.val.val.epsilon state.val.val.field)
    (originalCofactorFamily_estimate parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small).actualCoherent
    lower positive bounded radius inside angles
  rw [physicalMatrixProduct_apply,originalCofactorFamily_eq_signedCofactor parameters length state.val.val.rho state.val.val.epsilon state.val.val.field small,
    SmoothLowPhysicalRow.fullField_cartesianCovariant bounded _ radius inside angles] at native
  exact native.trans (sameCartesianCofactorFlux_literal parameters length compact lower positive bounded state curves radius inside angles).symm

/-- The cofactor reconstruction identity holds on the actual Cartesian collar, so all genuine derivatives agree there. -/
theorem sameCompletedCofactor_cartesian (point : SpatialPlane × ℝ) (inside : ‖point.1‖ ∈ Icc lower 1) :
    (sameCompletedCofactorCurves parameters length compact lower positive bounded state small curves).cartesianField bounded point =
      (samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.cartesianField bounded point := by
  let closed : ClosedDisk := ⟨point.1,inside.2⟩
  obtain ⟨angle,polar⟩ := Grad.Constraints.closedPoint_has_polar_angle closed
  have represented : polarPlane (‖point.1‖,angle) = point.1 := by
    have coordinates := congrArg Subtype.val polar
    rw [Grad.Constraints.polarClosedPoint_coordinates] at coordinates
    simpa only [polarPlane,Grad.BoundaryTrace.collarPlane,closed,sub_sub_cancel] using coordinates
  have first := (sameCompletedCofactorCurves parameters length compact lower positive bounded state small curves).cartesianField_polar bounded
    ‖point.1‖ (positive.trans_le inside.1) angle point.2
  have second := (samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.cartesianField_polar bounded
    ‖point.1‖ (positive.trans_le inside.1) angle point.2
  rw [polarPlane_originalParametrization,represented] at first second
  exact first.trans ((sameCompletedCofactor_fullField parameters length compact lower positive bounded state small curves ‖point.1‖ inside (angle,point.2)).trans second.symm)

theorem sameCompletedCofactor_fderiv (point : SpatialPlane × ℝ) (inside : ‖point.1‖ ∈ Ioo lower 1) :
    fderiv ℝ ((sameCompletedCofactorCurves parameters length compact lower positive bounded state small curves).cartesianField bounded) point =
      fderiv ℝ ((samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.cartesianField bounded) point := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [((isOpen_Ioo.preimage continuous_norm).prod isOpen_univ).mem_nhds
    (show point ∈ {query : SpatialPlane | ‖query‖ ∈ Ioo lower 1} ×ˢ (univ : Set ℝ) from ⟨inside,mem_univ _⟩)] with query member
  exact sameCompletedCofactor_cartesian parameters length compact lower positive bounded state small curves query ⟨member.1.1.le,member.1.2.le⟩

end Grad.ActualScalarWeakEquations
