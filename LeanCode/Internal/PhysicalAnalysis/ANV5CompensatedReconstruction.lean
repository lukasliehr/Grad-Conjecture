import ANV4StoredVectorScalar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
open Grad.ActualMeanInverse
variable {L sigma gamma ell : ℝ}

def reconstructionLoad (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (force : APSmooth L sigma gamma ell 2) : APSmooth L sigma gamma ell 2 :=
  (2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta) + force

def reconstructedVector (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (force : APSmooth L sigma gamma ell 2) : APSmooth L sigma gamma ell 2 :=
  -apVectorInverse admissible (reconstructionLoad admissible theta force)

def reconstructedScalar (admissible : Admissible L sigma gamma ell)
    (source : APSmooth L sigma gamma ell 1) : APSmooth L sigma gamma ell 1 := apShiftInverse admissible 0 source

/-- Literal AN12 compensated coordinates, on the actual original AP carriers. -/
def reconstructedState (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) : CompensatedData L sigma gamma ell :=
  (theta, storedPair L sigma gamma ell (reconstructedVector admissible theta source.1)
    (reconstructedScalar admissible source.2.2))

theorem reconstructedState_planar (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) :
    apSmoothPlanar L sigma gamma ell (reconstructedState admissible theta source).2 =
      reconstructedVector admissible theta source.1 := storedPair_planar admissible _ _

theorem reconstructedState_scalar (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell) :
    apSmoothScalar L sigma gamma ell (reconstructedState admissible theta source).2 =
      reconstructedScalar admissible source.2.2 := storedPair_scalar admissible _ _

private theorem force_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (row : E →ₗ[ℂ] E) (gradient force inverse : E) (equation : row inverse = (2 : ℂ) • gradient + force) :
    (-2 : ℂ) • gradient - row (-inverse) = force := by
  rw [map_neg, equation]
  module

theorem reconstructedState_forceInner (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (nonresonant : VectorNonresonant admissible (reconstructionLoad admissible theta source.1)) :
    circularForceInner admissible (reconstructedState admissible theta source) = source.1 := by
  have planar := reconstructedState_planar admissible theta source
  have equation := apVectorInverse_solves admissible (reconstructionLoad admissible theta source.1) nonresonant
  exact (congrArg (fun vector : APSmooth L sigma gamma ell 2 =>
      (-2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta) - vectorRotation admissible vector) planar).trans
    (force_algebra (vectorRotation admissible) (apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible theta))
      source.1 (apVectorInverse admissible (reconstructionLoad admissible theta source.1)) equation)

theorem reconstructedState_force (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (nonresonant : VectorNonresonant admissible (reconstructionLoad admissible theta source.1)) :
    circularForce admissible (reconstructedState admissible theta source) = source.1 :=
  (congrArg (apSmoothQrad L sigma gamma ell) (reconstructedState_forceInner admissible theta source nonresonant)).trans
    (actualSource_conditions admissible source compatible).1.1

private theorem abstract_shift_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (rotation : E →ₗ[ℂ] E) : rotation + (Complex.I * ((0 : ℤ) : ℂ)) • LinearMap.id = rotation := by
  simp

theorem apShiftedRotation_zero (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) :
    apShiftedRotation admissible dimension 0 field = apSmoothRotation admissible dimension field :=
  congrArg (fun mapping : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension => mapping field)
    (abstract_shift_zero (apSmoothRotation admissible dimension))

theorem reconstructedScalar_rotates (admissible : Admissible L sigma gamma ell)
    (source : APSmooth L sigma gamma ell 1) (nonresonant : APNonresonant admissible 0 source) :
    apSmoothRotation admissible 1 (reconstructedScalar admissible source) = source :=
  (apShiftedRotation_zero admissible (apShiftInverse admissible 0 source)).symm.trans
    (apShiftInverse_solves admissible 0 source nonresonant)

theorem reconstructedState_third (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) :
    circularThird admissible (reconstructedState admissible theta source) = source.2.2 :=
  (congrArg (apSmoothRotation admissible 1) (reconstructedState_scalar admissible theta source)).trans
    (reconstructedScalar_rotates admissible source.2.2 (actualSource_conditions admissible source compatible).2.2.1)

end Grad.ActualNonexceptionalInverse
