import Q23SeedScalarDerivativeTower
import TameChartGenuine
import RootUnitTower

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Seed

variable {phase : PhaseParameters}

/-- The literal finite-seed plus curvature/chart core input. -/
abbrev Q23MixedInput (phase : PhaseParameters) : Type :=
  Seed.Parameters × JointState phase

/-- Mathlib prepends derivative directions; the Q23 core tower presents them
in the paper's newest-last order. -/
def q23SeedFieldDirectionalCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 3 :=
  q23SeedFieldCoreDerivative phase order parameter (fun position => directions position.rev)

def q23SeedScalarDirectionalCoreDerivative (phase : PhaseParameters) (order : ℕ)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters) :
    ACore phase 1 :=
  q23SeedScalarCoreDerivative phase order parameter (fun position => directions position.rev)

def q23SeedTransferDirectionalCoreDerivative (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (order : ℕ) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) : ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  q23SeedTransferCoreDerivative phase reference insideR order parameter
    (fun position => directions position.rev)

/-- The root coefficient multiplied by the moving seed field, with every
mixed direction allocated to exactly one of the two factors. -/
def q23MixedRootSeedField (phase : PhaseParameters) (order : ℕ)
    (base : Q23MixedInput phase) (directions : Fin order → Q23MixedInput phase) :
    ACore phase 3 :=
  ∑ assignment : Fin order → Fin 2,
    tameScalarMultiplier 3
      (rootDerivativeFamily (assignmentFiber assignment 0).card base.2.2.1
        (fun position =>
          (q23FiberTuple assignment 0 directions position).2.2.1))
      (q23SeedFieldDirectionalCoreDerivative phase
        (assignmentFiber assignment 1).card base.1
        (fun position => (q23FiberTuple assignment 1 directions position).1))

/-- Affine tangential field: base at order zero, newest direction at order
one, and zero at every higher order. -/
def q23MixedTangentAffine (phase : PhaseParameters) :
    (order : ℕ) → Q23MixedInput phase →
      (Fin order → Q23MixedInput phase) → ACore phase 3
  | 0, base, _ => chartTangentPart phase base.2.2.1
  | 1, _, directions => chartTangentPart phase (directions 0).2.2.1
  | _ + 2, _, _ => 0

/-- Affine vector slot of the chart state. -/
def q23MixedVectorAffine (phase : PhaseParameters) :
    (order : ℕ) → Q23MixedInput phase →
      (Fin order → Q23MixedInput phase) → ACore phase 3
  | 0, base, _ => base.2.2.2.1
  | 1, _, directions => (directions 0).2.2.2.1
  | _ + 2, _, _ => 0

/-- Every derivative of `T_p v`, with directions allocated between the
moving seed operator and the affine vector slot. -/
def q23MixedTransferredVector (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (order : ℕ) (base : Q23MixedInput phase)
    (directions : Fin order → Q23MixedInput phase) : ACore phase 3 :=
  ∑ assignment : Fin order → Fin 2,
    q23SeedTransferDirectionalCoreDerivative phase reference insideR
      (assignmentFiber assignment 0).card base.1
      (fun position => (q23FiberTuple assignment 0 directions position).1)
      (q23MixedVectorAffine phase (assignmentFiber assignment 1).card base
        (q23FiberTuple assignment 1 directions))

/-- Affine potential slot of the chart state. -/
def q23MixedPotentialAffine (phase : PhaseParameters) :
    (order : ℕ) → Q23MixedInput phase →
      (Fin order → Q23MixedInput phase) → ACore phase 1
  | 0, base, _ => base.2.2.2.2
  | 1, _, directions => (directions 0).2.2.2.2
  | _ + 2, _, _ => 0

/-- The actual mixed inner derivative family before the unchanged quotient
polynomial: curvature, chart field, and chart potential. -/
def q23MixedReferenceFamily (phase : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (order : ℕ) (base : Q23MixedInput phase)
    (directions : Fin order → Q23MixedInput phase) : QuotientState phase :=
  (referenceScalar order base.2 (fun position => (directions position).2),
    (q23MixedRootSeedField phase order base directions +
        q23MixedTangentAffine phase order base directions +
        q23MixedTransferredVector phase reference insideR order base directions,
      q23SeedScalarDirectionalCoreDerivative phase order base.1
          (fun position => (directions position).1) +
        q23MixedPotentialAffine phase order base directions))

end Grad.NonlinearQuotientBounds
