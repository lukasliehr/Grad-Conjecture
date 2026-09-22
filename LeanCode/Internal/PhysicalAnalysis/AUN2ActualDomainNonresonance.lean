import AUN1ActualVectorUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.ActualReconstructionUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Envelope
open Grad.ActualAngularInverse Grad.ActualNonexceptionalInverse Grad.RawCircularSectors
variable {L sigma gamma ell : ℝ}

theorem originalState_planar_nonresonant (admissible : Admissible L sigma gamma ell)
    (state : CompensatedData L sigma gamma ell) (excluded : AvoidsExceptionalState state) :
    VectorNonresonant admissible (apSmoothPlanar L sigma gamma ell state.2) := by
  have component (sign : ℤ) (signed : sign = 1 ∨ sign = -1) :
      APNonresonant admissible sign (apHelicity L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2)) := by
    apply rawExclusion_nonresonant admissible _ sign signed
    have exceptional : IsExceptionalRaw (-2 * sign) := by rcases signed with rfl | rfl <;> norm_num [IsExceptionalRaw]
    apply apSmoothJet_ext admissible
    intro cell
    exact (apSmoothRawVector_jet admissible (-2 * sign) _ cell).trans
      ((rawState_excluded_components admissible (-2 * sign) state (excluded _ exceptional) cell).2.1.trans (map_zero _).symm)
  exact ⟨component 1 (Or.inl rfl), component (-1) (Or.inr rfl)⟩

/-- The scalar mean condition is derived from the actual original circular
complement condition, not imposed as a new inverse hypothesis. -/
theorem originalState_scalar_nonresonant (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) :
    APNonresonant admissible 0 (apSmoothScalar L sigma gamma ell state.val.2) := by
  have complement := circularRemainder_complement_zero admissible state
  have meanZero := (apSmoothScalar_complement admissible state.val.2).symm.trans
    ((congrArg (apSmoothScalar L sigma gamma ell) complement).trans (map_zero _))
  intro cell
  change angularClosedJet 0 (apSmoothJet admissible 1 cell (apSmoothScalar L sigma gamma ell state.val.2)) = 0
  exact (apSmoothAngularMean_jet admissible _ cell).symm.trans
    ((congrArg (apSmoothJet admissible 1 cell) meanZero).trans (map_zero _))

theorem originalState_scalar_unique (admissible : Admissible L sigma gamma ell)
    (state : circularCompensatedCore admissible) (source : APSmooth L sigma gamma ell 1)
    (third : circularThird admissible state.val = source) :
    apSmoothScalar L sigma gamma ell state.val.2 = reconstructedScalar admissible source :=
  apShiftInverse_unique admissible 0 source _ (originalState_scalar_nonresonant admissible state)
    ((apShiftedRotation_zero admissible (apSmoothScalar L sigma gamma ell state.val.2)).trans third)

end Grad.ActualReconstructionUniqueness
