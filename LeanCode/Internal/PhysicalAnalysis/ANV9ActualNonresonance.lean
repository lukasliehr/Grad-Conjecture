import ANV8AxisPreservation
import ANP16ActualSectorConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
open Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

def ScalarAvoidsExceptional (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) : Prop :=
  ∀ cell mode, IsExceptionalRaw mode → angularClosedJet mode (apSmoothJet admissible 1 cell field) = 0

theorem rawVectorJet_helicity (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (mode : ℤ) (field : ClosedJet 2) :
    valueMapJet (helicityValue sign) (rawVectorJet mode field) =
      angularClosedJet (mode + sign) (valueMapJet (helicityValue sign) field) := by
  rcases signed with rfl | rfl
  · simp only [helicityValue_positive, rawVectorJet_eq, valueMapJet_add, valueMapJet_comp,
      positiveHelicity_idempotent, positiveHelicity_negative, valueMapJet_zero, add_zero,
      angularClosedJet_valueMap]
  · simp only [helicityValue_negative, rawVectorJet_eq, valueMapJet_add, valueMapJet_comp,
      negativeHelicity_idempotent, negativeHelicity_positive, valueMapJet_zero, zero_add,
      angularClosedJet_valueMap, sub_eq_add_neg]

theorem apSmoothRawVector_gradient (admissible : Admissible L sigma gamma ell)
    (mode : ℤ) (theta : APSmooth L sigma gamma ell 1) :
    apSmoothRawVector L sigma gamma ell mode (apSmoothGradient admissible theta) =
      apSmoothGradient admissible (apSmoothAngularMode L sigma gamma ell 1 mode theta) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRawVector_jet admissible mode _ cell).trans
    ((congrArg (rawVectorJet mode) (apSmoothGradient_jet admissible theta cell)).trans
      ((gradientJet_angular mode _).symm.trans
        ((congrArg gradientJet (apSmoothAngularMode_jet admissible mode theta cell).symm).trans
          (apSmoothGradient_jet admissible _ cell).symm)))

theorem scalarAvoids_projector_zero (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (excluded : ScalarAvoidsExceptional admissible theta)
    (mode : ℤ) (exceptional : IsExceptionalRaw mode) : apSmoothAngularMode L sigma gamma ell 1 mode theta = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothAngularMode_jet admissible mode theta cell).trans
    ((excluded cell mode exceptional).trans (map_zero _).symm)

private theorem projected_load_zero {E S : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup S] [Module ℂ S] (project quarter : E →ₗ[ℂ] E)
    (gradient : S →ₗ[ℂ] E) (theta : S) (force : E)
    (turned : ∀ value, project (quarter value) = quarter (project value))
    (gradZero : project (gradient theta) = 0) (forceZero : project force = 0) :
    project ((2 : ℂ) • quarter (gradient theta) + force) = 0 := by
  rw [map_add, map_smul, turned, gradZero, map_zero, smul_zero, forceZero, add_zero]

theorem reconstructionLoad_excluded (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source)
    (mode : ℤ) (exceptional : IsExceptionalRaw mode) :
    apSmoothRawVector L sigma gamma ell mode (reconstructionLoad admissible theta source.1) = 0 := by
  have gradientZero := (apSmoothRawVector_gradient admissible mode theta).trans
    ((congrArg (apSmoothGradient admissible) (scalarAvoids_projector_zero admissible theta thetaExcluded mode exceptional)).trans
      (map_zero _))
  exact projected_load_zero (apSmoothRawVector L sigma gamma ell mode) (apSmoothQuarter L sigma gamma ell)
    (apSmoothGradient admissible) theta source.1 (apSmoothRawVector_quarter admissible mode) gradientZero
    (congrArg Prod.fst (sourceExcluded mode exceptional))

theorem rawExclusion_nonresonant (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 2) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (excluded : apSmoothRawVector L sigma gamma ell (-2 * sign) field = 0) :
    APNonresonant admissible sign (apHelicity L sigma gamma ell sign field) := by
  intro cell
  have rawZero := (apSmoothRawVector_jet admissible (-2 * sign) field cell).symm.trans
    ((congrArg (apSmoothJet admissible 2 cell) excluded).trans (map_zero _))
  have projected := (rawVectorJet_helicity sign signed (-2 * sign) (apSmoothJet admissible 2 cell field)).symm.trans
    ((congrArg (valueMapJet (helicityValue sign)) rawZero).trans (valueMapJet_map_zero _))
  have index : -2 * sign + sign = -sign := by omega
  rw [index] at projected
  exact (congrArg (angularClosedJet (-sign)) (apSmoothValueMap_jet admissible (helicityValue sign) field cell)).trans projected

/-- Both inverse resonances are removed by the actual raw-sector exclusions;
there is no independent nonresonance premise on the reconstructed load. -/
theorem reconstructionLoad_nonresonant (admissible : Admissible L sigma gamma ell)
    (theta : APSmooth L sigma gamma ell 1) (source : SmoothCapSource L sigma gamma ell)
    (thetaExcluded : ScalarAvoidsExceptional admissible theta) (sourceExcluded : AvoidsExceptionalSource source) :
    VectorNonresonant admissible (reconstructionLoad admissible theta source.1) := by
  constructor
  · apply rawExclusion_nonresonant admissible _ 1 (Or.inl rfl)
    exact reconstructionLoad_excluded admissible theta source thetaExcluded sourceExcluded _ (by norm_num [IsExceptionalRaw])
  · apply rawExclusion_nonresonant admissible _ (-1) (Or.inr rfl)
    exact reconstructionLoad_excluded admissible theta source thetaExcluded sourceExcluded _ (by norm_num [IsExceptionalRaw])

end Grad.ActualNonexceptionalInverse
