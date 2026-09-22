import ASX21ActualExceptionalDomain
import ASX22SignedRowAlgebra

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.ActualCenterVolterra
open Grad.NonlinearRange Grad.RawCircularSectors Grad.FlatSourceProjection Grad.ActualMeanInverse
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

theorem exceptionalState_forceInner (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    circularForceInner admissible (exceptionalState admissible sign source) = source.1 := by
  have modes := exceptionalState_planar_modes admissible sign signed source raw
  apply smoothSpin_ext admissible sign signed
  · have rotates : apSmoothRotation admissible 1 (smoothSpin L sigma gamma ell sign
        (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2)) =
        (Complex.I * ((2 * sign + sign : ℤ) : ℂ)) • smoothSpin L sigma gamma ell sign
          (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2) := by
      simpa only [show 2 * sign + sign = 3 * sign by omega] using smoothMode_rotation admissible (3 * sign) _ modes.1
    have stored := (exceptionalState_spin admissible sign sign source).trans
      (congrArg (fun value : APSmooth L sigma gamma ell 1 =>
        value - smoothSignedDerivative admissible 1 (-sign) (exceptionalTheta admissible sign source))
        (exceptionalPlanar_first admissible sign signed source))
    exact (smoothSpin_force_mode admissible (2 * sign) sign signed (exceptionalState admissible sign source) rotates).trans
      ((congrArg (fun value : APSmooth L sigma gamma ell 1 =>
        (-2 * Complex.I * (sign : ℂ)) • smoothSignedDerivative admissible 1 (-sign) (exceptionalTheta admissible sign source) -
          (Complex.I * ((2 * sign + 2 * sign : ℤ) : ℂ)) • value) stored).trans
        (exceptionalPositiveForce_algebra sign signed (smoothSignedDerivative admissible 1 (-sign))
          (exceptionalPsi admissible sign source) (smoothSpin L sigma gamma ell sign source.1)))
  · have rotates : apSmoothRotation admissible 1 (smoothSpin L sigma gamma ell (-sign)
        (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2)) =
        (Complex.I * ((2 * sign + -sign : ℤ) : ℂ)) • smoothSpin L sigma gamma ell (-sign)
          (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2) := by
      simpa only [show 2 * sign + -sign = sign by omega] using smoothMode_rotation admissible sign _ modes.2
    have algebra := exceptionalNegativeForce_algebra sign signed (smoothSignedDerivative admissible 1 (- -sign))
      (exceptionalPsi admissible sign source)
      (smoothSpin L sigma gamma ell (-sign) (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2))
    have row := (smoothSpin_force_mode admissible (2 * sign) (-sign) (by omega) (exceptionalState admissible sign source) rotates).trans algebra
    simpa only [neg_neg] using row.trans (by simpa only [neg_neg] using exceptionalPsi_equation admissible sign signed source raw)

theorem exceptionalState_force (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (raw : IsRawSourceSector admissible (2 * sign) source) :
    circularForce admissible (exceptionalState admissible sign source) = source.1 :=
  (congrArg (apSmoothQrad L sigma gamma ell) (exceptionalState_forceInner admissible sign signed source raw)).trans
    (actualSource_conditions admissible source compatible).1.1

theorem exceptionalState_third (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    circularThird admissible (exceptionalState admissible sign source) = source.2.2 :=
  (congrArg (apSmoothRotation admissible 1) (exceptionalState_scalar admissible sign source)).trans
    (exceptionalThird_algebra sign signed (apSmoothRotation admissible 1) source.2.2
      (smoothMode_rotation admissible (2 * sign) source.2.2 raw.2.2))

theorem removeMean_of_meanZero (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (meanZero : APSmoothMeanZero admissible field) :
    apSmoothRemoveMean L sigma gamma ell 1 field = field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRemoveMean_jet admissible field cell).trans
    ((congrArg (fun jet : ClosedJet 1 => apSmoothJet admissible 1 cell field - jet) (meanZero cell)).trans (sub_zero _))

private theorem negative_removeMean {E : Type*} [AddCommGroup E] [Module ℂ E]
    (project : E →ₗ[ℂ] E) (field : E) (fixed : project field = field) : -project (-field) = field := by
  rw [map_neg, fixed, neg_neg]

theorem exceptionalState_determinant (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (raw : IsRawSourceSector admissible (2 * sign) source) :
    circularDeterminant admissible (exceptionalState admissible sign source) = source.2.1 :=
  (congrArg (fun value : APSmooth L sigma gamma ell 1 => -apSmoothRemoveMean L sigma gamma ell 1 value)
    (exceptionalState_divergence admissible sign signed source (exceptionalFreeSpin_equation admissible sign signed source raw))).trans
      (negative_removeMean (apSmoothRemoveMean L sigma gamma ell 1) source.2.1
        (removeMean_of_meanZero admissible source.2.1 (actualSource_conditions admissible source compatible).2.1))

/-- All three interior rows are the original circular rows on the original compatible source. -/
theorem exceptionalState_rows (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (raw : IsRawSourceSector admissible (2 * sign) source) :
    circularRows admissible (exceptionalState admissible sign source) = source :=
  Prod.ext (exceptionalState_force admissible sign signed source compatible raw)
    (Prod.ext (exceptionalState_determinant admissible sign signed source compatible raw)
      (exceptionalState_third admissible sign signed source raw))

theorem exceptionalState_radialMode (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (2 * sign)
      (apSmoothRadial admissible (compensatedReconstruct admissible (exceptionalState admissible sign source))) := by
  have modes := exceptionalPlanar_modes admissible sign signed source raw
  intro cell
  have total := exceptionalState_reconstruct admissible sign source
  have planar := (apSmoothValueMap_jet admissible planarPartMap
    (compensatedReconstruct admissible (exceptionalState admissible sign source)) cell).symm.trans
      (congrArg (apSmoothJet admissible 2 cell)
        ((congrArg (apSmoothPlanar L sigma gamma ell) total).trans (exceptionalCovariant_planar admissible sign source)))
  have first := (congrArg (valueMapJet (spinValue (sign : ℂ))) planar).trans
    (smoothSpin_jet admissible sign (exceptionalPlanar admissible sign source) cell).symm
  have second := (congrArg (valueMapJet (spinValue ((-sign : ℤ) : ℂ))) planar).trans
    (smoothSpin_jet admissible (-sign) (exceptionalPlanar admissible sign source) cell).symm
  have law := apSmoothFixedJet_jet admissible radialRowJet
    (compensatedReconstruct admissible (exceptionalState admissible sign source)) cell
  exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet (2 * sign) jet = jet) law).mpr
    (radialRow_secondMode sign signed _
    ((congrArg (fun jet : ClosedJet 1 => angularClosedJet (3 * sign) jet = jet) first).mpr (modes.1 cell))
    ((congrArg (fun jet : ClosedJet 1 => angularClosedJet sign jet = jet) second).mpr (modes.2 cell)))

/-- The fourth, literal high boundary row vanishes at every allowed original trace grade. -/
theorem exceptionalState_highBoundary (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (grade : ℕ) (large : 1 ≤ grade) :
    circularCoreTrace admissible grade (exceptionalState admissible sign source) = 0 :=
  apHighTrace_lowMode_zero admissible (2 * sign) (by rcases signed with rfl | rfl <;> norm_num) _
    (exceptionalState_radialMode admissible sign signed source raw) (grade + 1) (by omega)

end Grad.ActualExceptionalInverse
