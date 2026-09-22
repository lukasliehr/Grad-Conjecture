import AUN2ActualDomainNonresonance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.ActualReconstructionUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Envelope
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

private theorem force_unique_algebra {E : Type*} [AddCommGroup E] [Module ℂ E]
    (gradient rotated force : E) (equation : (-2 : ℂ) • gradient - rotated = force) :
    rotated = -((2 : ℂ) • gradient + force) := by
  rw [← equation]
  module

theorem originalState_planar_unique (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (force : APSmooth L sigma gamma ell 2)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (sameTheta : state.val.1 = theta) (sameForce : circularForce admissible state.val = force) :
    apSmoothPlanar L sigma gamma ell state.val.2 = reconstructedVector admissible theta force := by
  have inner := (circularForce_eq_inner admissible state).symm.trans sameForce
  change (-2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible state.val.1) -
    vectorRotation admissible (apSmoothPlanar L sigma gamma ell state.val.2) = force at inner
  have replaced := (congrArg (fun potential : APSmooth L sigma gamma ell 1 =>
    (-2 : ℂ) • apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible potential) -
      vectorRotation admissible (apSmoothPlanar L sigma gamma ell state.val.2)) sameTheta).symm.trans inner
  have equation := force_unique_algebra _ _ _ replaced
  exact (apVectorInverse_unique admissible (-(reconstructionLoad admissible theta force)) _
    (originalState_planar_nonresonant admissible state.val excluded) equation).trans
      (map_neg (apVectorInverse admissible) (reconstructionLoad admissible theta force))

theorem closedStored_reconstruction (field : ClosedJet 3) :
    valueMapJet planarInclusionMap (valueMapJet planarPartMap field) +
      valueMapJet toroidalInclusionMap (valueMapJet toroidalPartMap field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have identity := congrArg (fun mapping : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 => mapping (field.value point)) splitting_reconstruction
  simpa only [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using identity

theorem storedPair_reconstruction (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 3) :
    storedPair L sigma gamma ell (apSmoothPlanar L sigma gamma ell field) (apSmoothScalar L sigma gamma ell field) = field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (storedPair_jet admissible (apSmoothPlanar L sigma gamma ell field) (apSmoothScalar L sigma gamma ell field) cell).trans
    ((congrArg₂ (fun first second : ClosedJet 3 => first + second)
      (congrArg (valueMapJet planarInclusionMap) (apSmoothValueMap_jet admissible planarPartMap field cell))
      (congrArg (valueMapJet toroidalInclusionMap) (apSmoothValueMap_jet admissible toroidalPartMap field cell))).trans
        (closedStored_reconstruction _))

/-- Any actual original circular state with the required raw exclusions is
exactly the ANV reconstruction when theta, force and third row agree.
There is no newly assumed resonance, mean, or source compatibility condition. -/
theorem originalReconstruction_unique (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (state : circularCompensatedCore admissible) (excluded : AvoidsExceptionalState state.val)
    (sameTheta : state.val.1 = theta) (sameForce : circularForce admissible state.val = source.1)
    (sameThird : circularThird admissible state.val = source.2.2) :
    state.val = reconstructedState admissible theta source := by
  apply Prod.ext sameTheta
  exact (storedPair_reconstruction admissible state.val.2).symm.trans
    (congrArg₂ (storedPair L sigma gamma ell)
      (originalState_planar_unique admissible theta source.1 state excluded sameTheta sameForce)
      (originalState_scalar_unique admissible state source.2.2 sameThird))

end Grad.ActualReconstructionUniqueness
