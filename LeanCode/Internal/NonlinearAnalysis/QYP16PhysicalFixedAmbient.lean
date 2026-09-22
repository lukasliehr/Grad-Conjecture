import QYP15PhysicalFixedInner
import QYP11PhysicalForwardGrades

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

open scoped ContDiff

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.AxisCore Grad.QuotientProjection

def jointAtSeed (parameters : PhaseParameters) (grade : ℕ) (seed : Seed.Parameters)
    (state : JointAmbient parameters grade) : MixedAmbient parameters grade :=
  WithLp.toLp 1 (WithLp.toLp 1 seed, state)

theorem jointAtSeed_contDiff (parameters : PhaseParameters) (grade : ℕ) (seed : Seed.Parameters) :
    ContDiff ℝ ∞ (jointAtSeed parameters grade seed) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1 (JointAmbient parameters grade)).symm.contDiff.comp
    (contDiff_const.prodMk contDiff_id)

def completedPhysicalFixedSlice (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (_insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (_insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : JointAmbient parameters (grade + 6)) : ZAmbient parameters grade :=
  completedPhysicalMixedSlice parameters cellLength reference grade (jointAtSeed parameters (grade + 6) seed state)

theorem completedPhysicalFixedSlice_contDiffOn (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade)
      (jointDomain parameters (grade + 6)) :=
  (completedPhysicalMixedSlice_contDiffOn parameters cellLength reference grade).comp
    (jointAtSeed_contDiff parameters (grade + 6) seed).contDiffOn (fun _ member => ⟨insideS, member⟩)

theorem completedPhysicalFixedSlice_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (grade : ℕ)
    (state : JointState parameters) (axis : ChartAxisCondition state.2) :
    completedPhysicalFixedSlice parameters cellLength reference insideR seed insideS grade
      (jointCoreEmbed parameters (grade + 6) state) =
      quotientEta parameters grade (physicalFixedSliceMap parameters cellLength reference insideR seed insideS state) :=
  completedPhysicalMixedSlice_core parameters cellLength reference insideR grade (seed, state) insideS axis

def physicalFixedSliceDerivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    (order : ℕ) → JointState parameters → (Fin order → JointState parameters) → QuotientRows parameters :=
  NonlinearQuotientBounds.composedDerivative
    (physicalFixedReferenceFamily parameters reference insideR seed insideS) cellLength

end Grad.PhysicalCoordinates
