import AKBC46ActualReconstructedForceConsumer
import QO6RadialMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift
open Grad.OriginalKernelRetainedDecay

theorem originalVariationRadialCorrection_mean {parameters : PhaseParameters}
    (field vector : ACore parameters 3) :
    radiusSquaredCore parameters (physicalVariationRadialCorrection field vector)=
      angularCore parameters 0
        (dotOperation parameters (eulerCore parameters vector) (rotationCore parameters field)+
          dotOperation parameters (eulerCore parameters field) (rotationCore parameters vector)) := by
  have mixed := quotientDot_radial_identity (field+vector)
  have base := quotientDot_radial_identity field
  have varied := quotientDot_radial_identity vector
  simp only [map_add,LinearMap.add_apply] at mixed
  simp only [physicalVariationRadialCorrection,map_add]
  apply add_left_cancel (a:=angularCore parameters 0 (dotOperation parameters (eulerCore parameters field) (rotationCore parameters field)))
  apply add_right_cancel (b:=angularCore parameters 0 (dotOperation parameters (eulerCore parameters vector) (rotationCore parameters vector)))
  rw [base,varied] at mixed
  convert mixed using 1 <;> abel

/-- The radial correction in the actual original derivative is angularly
constant after multiplication by the literal squared radius. -/
theorem originalVariationRadialCorrection_projected {parameters : PhaseParameters}
    (field vector : ACore parameters 3) :
    removeAngularCore parameters (radiusSquaredCore parameters (physicalVariationRadialCorrection field vector))=0 := by
  rw [originalVariationRadialCorrection_mean]
  simp only [removeAngularCore,LinearMap.sub_apply,LinearMap.id_apply,angularCore_projection,ite_true,sub_self]

end Grad.OriginalKernelHomogeneousGraph
