import AKBU16OriginalPhysicalVectorCircleZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.SourceCollarFullSource Grad.OriginalKernelRetainedDecay
open Grad.NonlinearQuotientBounds Grad.Constraints Grad.Cor18 Grad.AxisSplit Grad.NonlinearRange

/-- Original closed Cartesian core fidelity, using all original axial
Fourier cells and the accepted full closed-disk polar coverage. -/
theorem originalCore_zero_of_positiveCircles {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (axis : ∀ cell,originValue (field.val cell)=0)
    (circles : ∀ radius : RadialPoint,0<radius.val→∀ angles,originalCoreCircle parameters field radius angles=0) :
    field=0 := by
  apply acore_ext
  intro cell point
  change (field.val cell).value point=0
  by_cases origin : point.val=0
  · have same : point=originPoint := Subtype.ext origin
    rw [same]
    exact axis cell
  · obtain ⟨angle,same⟩ := closedPoint_has_polar_angle point
    have equality : (fun axial => originalCoreCircle parameters field ⟨‖point.val‖,norm_nonneg _,point.property⟩ (angle,axial))=fun _ => 0 :=
      funext (fun axial => circles _ (norm_pos_iff.mpr origin) (angle,axial))
    have coefficient := congrArg (fun source : ℝ→ComplexEuclidean dimension => Grad.BoundaryTrace.angularCoefficient source cell) equality
    rw [originalCoreCircle_axialCoefficient,Grad.BoundaryTrace.angularCoefficient_zero,divisionPolarPoint_eq_original,same] at coefficient
    exact coefficient

end Grad.OriginalPhysicalKernelUniqueness
