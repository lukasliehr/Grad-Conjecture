import AKCP6ActualOriginalFullForward
import AKU80RealOriginalDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Cor18 Grad.CompletedReality Grad.PhysicalCoordinates Grad.FinitePhysicalJetLift

/-- The difference from ordinary physical conjugation keeps all original
vector constraints, including the physical outer row, and the scalar mean. -/
theorem originalConjugateDifference_constraints (parameters : PhaseParameters)
    (seed : Seed.Parameters) (inside : seed∈Seed.parameterDomain)
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters seed inside (toPhysicalCore parameters vector))
    (mean : angularCore parameters 0 scalar=0) :
    VectorConstraints parameters seed inside
      (toPhysicalCore parameters (vector-cartesianCoreConjugation parameters vector)) ∧
    angularCore parameters 0 (scalar-cartesianCoreConjugation parameters scalar)=0 := by
  constructor
  · rw [map_sub,← toPhysicalCore_conjugate]
    have fixed := vectorProjection_fixes parameters seed inside (toPhysicalCore parameters vector) constrained
    apply (vectorProjection_range_iff parameters seed inside _).mp
    refine ⟨toPhysicalCore parameters vector-cartesianCoreConjugation parameters (toPhysicalCore parameters vector),?_⟩
    rw [map_sub,← vectorProjection_conjugate,fixed]
  · have commute := angularCore_conjugate parameters 0 scalar
    simp only [neg_zero] at commute
    rw [map_sub,← commute,mean,map_zero,sub_self]

end Grad.OriginalCoreRealization
