import ANV9ActualNonresonance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange Grad.NonlinearDivision
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
open Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

theorem closedGradient_firstJet_of_hessian (theta : ClosedJet 1) (flat : ClosedFirstJetZero theta)
    (hessian : ∀ first second, (partialJet first (partialJet second theta)).value closedOrigin = 0) :
    ClosedFirstJetZero (gradientJet theta) := by
  constructor
  · rw [gradientJet_value, flat.2 0, flat.2 1]
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp
  · intro direction
    rw [partialJet_gradient, closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value, valueMapJet_value,
      hessian direction 0, hessian direction 1, map_zero, map_zero, add_zero]

theorem scalarAvoids_gradient_firstJet (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (excluded : ScalarAvoidsExceptional admissible theta)
    (flat : APSmoothAxisFirstJetZero admissible theta) :
    APSmoothAxisFirstJetZero admissible (apSmoothGradient admissible theta) := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact (congrArg ClosedFirstJetZero (apSmoothGradient_jet admissible theta cell)).mpr
    (closedGradient_firstJet_of_hessian _ (apSmoothAxisFirstJetZero_closed admissible theta flat cell)
      (hessian_axis_zero_of_exceptional _ (excluded cell)))

theorem closedCovariant_firstJet_of_hessian (frequency : ℂ) (theta : ClosedJet 1) (flat : ClosedFirstJetZero theta)
    (hessian : ∀ first second, (partialJet first (partialJet second theta)).value closedOrigin = 0) :
    ClosedFirstJetZero (covariantJet frequency theta) := by
  refine ⟨covariantJet_axis_value frequency theta flat, ?_⟩
  intro direction
  rw [covariantJet_partial_value, hessian direction 0, hessian direction 1, flat.2 direction]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp

theorem scalarAvoids_covariant_firstJet (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (excluded : ScalarAvoidsExceptional admissible theta)
    (flat : APSmoothAxisFirstJetZero admissible theta) :
    APSmoothAxisFirstJetZero admissible (apSmoothCovariant admissible theta) := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact (congrArg ClosedFirstJetZero (apSmoothCovariant_jet admissible theta cell)).mpr
    (closedCovariant_firstJet_of_hessian _ _ (apSmoothAxisFirstJetZero_closed admissible theta flat cell)
      (hessian_axis_zero_of_exceptional _ (excluded cell)))

theorem excludedSource_force_firstJet (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (excluded : AvoidsExceptionalSource source) : APSmoothAxisFirstJetZero admissible source.1 := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact ⟨(Grad.ActualMeanInverse.actualSource_conditions admissible source compatible).1.2.1 cell,
    exceptionalSource_force_partial_zero admissible source excluded cell⟩

/-- The original AN7 axis condition is obtained from the genuine scalar pin
and the actual excluded modes; no independent flatness of v is imposed. -/
theorem reconstructedState_flatCore (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (thetaFlat : APSmoothAxisFirstJetZero admissible theta) :
    reconstructedState admissible theta source ∈ compensatedFlatCore admissible := by
  have covariantFlat := scalarAvoids_covariant_firstJet admissible theta thetaExcluded thetaFlat
  have storedFlat := reconstructedState_stored_firstJet admissible theta source compatible
    (scalarAvoids_gradient_firstJet admissible theta thetaExcluded thetaFlat)
    (excludedSource_force_firstJet admissible source compatible sourceExcluded)
  apply (mem_compensatedFlatCore admissible _).mpr
  refine ⟨⟨fun cell => thetaExcluded cell 0 (Or.inl rfl), thetaFlat⟩, ?_⟩
  exact (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible 3).add_mem
    ((mem_apSmoothAxisFirsts admissible _).mpr covariantFlat)
    ((mem_apSmoothAxisFirsts admissible _).mpr storedFlat))

end Grad.ActualNonexceptionalInverse
