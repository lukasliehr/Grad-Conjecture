import AKCH2OriginalProductDirections
import AKBC30OriginalCovariantCoreProduct
import AKBC2SamePolarCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.ActualSmoothPhysicalField Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay Grad.NonlinearRange
open Grad.ActualCurrentPrimitives Grad.ActualCartesianDescent Grad.SourceCollar

/-- Invert the already checked physical recovery: the native Cartesian
covariant is the literal original full-frame core F_C^T U. -/
theorem nativeCovariant_sameOriginalCore (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (nonzero : length≠0) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (vector : ACore parameters 3) (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ)
    (same : (curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).fullField bounded (radius,angles)=
      coreValue vector (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2) :
    coreValue (originalCovariantCore parameters length epsilon base vector false)
      (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
      curves.cartesianCovariant.fullField bounded (radius,angles) := by
  have inverse := Grad.ActualPhysicalField.originalInverseTransposeFamily_two_sided parameters length rho epsilon base small 0 angles.2
    (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)
  rw [originalCovariantCore_value parameters length epsilon nonzero base vector,← same,
    SmoothLowPhysicalRow.fullField_physicalUFromPolar parameters length rho epsilon base small lower positive bounded,
    SmoothLowPhysicalRow.fullField_cartesianCovariant bounded curves radius inside angles]
  change WithLp.toLp 2 (Matrix.mulVec _ (Matrix.mulVec _ _))=_
  rw [Matrix.mulVec_mulVec,inverse.1,Matrix.one_mulVec]
  exact inside

/-- The SAME original core and native closed collar values identify their
Cartesian representatives before derivatives are taken. -/
theorem originalCore_same_nativeCartesian {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (core : ACore parameters dimension)
    (same : ∀ (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ),
      coreValue core (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
        curves.fullField bounded (radius,angles))
    (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Icc lower 1) :
    coreValue core ⟨point.1,inside.2⟩ point.2=curves.cartesianField bounded point := by
  let closed : ClosedDisk := ⟨point.1,inside.2⟩
  obtain ⟨angle,polar⟩ := Grad.Constraints.closedPoint_has_polar_angle closed
  have represented : polarPlane (‖point.1‖,angle)=point.1 := by
    have coordinates := congrArg Subtype.val polar
    rw [Grad.Constraints.polarClosedPoint_coordinates] at coordinates
    simpa only [polarPlane,Grad.BoundaryTrace.collarPlane,closed,sub_sub_cancel] using coordinates
  have native := curves.cartesianField_polar bounded ‖point.1‖ (positive.trans_le inside.1) angle point.2
  rw [polarPlane_originalParametrization,represented] at native
  have corePoint : Grad.SourceCollarDivision.polarClosedPoint ‖point.1‖ angle (positive.le.trans inside.1) inside.2=closed := by
    apply Subtype.ext
    exact represented
  have value := same ‖point.1‖ inside (angle,point.2)
  rw [corePoint] at value
  exact value.trans native.symm

 theorem originalCore_same_nativeDerivative {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (core : ACore parameters dimension)
    (same : ∀ (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ),
      coreValue core (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) angles.2=
        curves.fullField bounded (radius,angles))
    (point : SpatialPlane×ℝ) (inside : ‖point.1‖∈Ioo lower 1) :
    fderiv ℝ (originalCoreProductLift parameters core) point=fderiv ℝ (curves.cartesianField bounded) point :=
  originalCoreProductLift_annular_fderiv parameters core lower _
    (originalCore_same_nativeCartesian parameters lower positive bounded curves core same) point inside

end Grad.OriginalCoreRealization
