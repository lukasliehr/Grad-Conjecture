import ASX24SmoothSectorUniqueness

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.RawCircularSectors Grad.FlatSourceProjection Grad.ActualMeanInverse
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

private theorem negative_force_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (gradient field : E)
    (equation : (-2 * Complex.I * ((-sign : ℤ) : ℂ)) • gradient -
      (Complex.I * ((2 * sign + 2 * -sign : ℤ) : ℂ)) • field = 0) : gradient = 0 := by
  have first : -2 * Complex.I * ((-sign : ℤ) : ℂ) = 2 * Complex.I * (sign : ℂ) := by push_cast; ring
  have second : Complex.I * ((2 * sign + 2 * -sign : ℤ) : ℂ) = 0 := by push_cast; ring
  rw [first, second, zero_smul, sub_zero] at equation
  exact (smul_eq_zero.mp equation).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (signedCast_nonzero sign signed))

private theorem positive_force_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (gradient field : E) (gradientZero : gradient = 0)
    (equation : (-2 * Complex.I * (sign : ℂ)) • gradient -
      (Complex.I * ((2 * sign + 2 * sign : ℤ) : ℂ)) • field = 0) : field = 0 := by
  have coefficient : Complex.I * ((2 * sign + 2 * sign : ℤ) : ℂ) = 4 * Complex.I * (sign : ℂ) := by push_cast; ring
  rw [gradientZero, smul_zero, zero_sub, neg_eq_zero, coefficient] at equation
  exact (smul_eq_zero.mp equation).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (signedCast_nonzero sign signed))

private theorem divergence_free_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (firstDerivative secondDerivative axial : E →ₗ[ℂ] E) (first second scalar : E)
    (firstZero : first = 0) (scalarZero : scalar = 0)
    (equation : (1 / 2 : ℂ) • (firstDerivative first + secondDerivative second) + axial scalar = 0) :
    secondDerivative second = 0 := by
  rw [firstZero, scalarZero, map_zero, map_zero, zero_add, add_zero] at equation
  exact (smul_eq_zero.mp equation).resolve_left (by norm_num)

/-- The actual raw exceptional kernel is zero in the original compensated domain.
The pin removes the only homogeneous first-spin solution. -/
theorem exceptionalKernel_zero (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (state : CompensatedData L sigma gamma ell)
    (domain : state ∈ circularCompensatedCore admissible)
    (raw : IsRawStateSector admissible (2 * sign) state) (rows : circularRows admissible state = 0) : state = 0 := by
  have forceZero : circularForceInner admissible state = 0 :=
    (circularForce_eq_inner admissible ⟨state, domain⟩).symm.trans
      (congrArg (fun source : SmoothCapSource L sigma gamma ell => source.1) rows)
  have thirdZero : apSmoothRotation admissible 1 (apSmoothScalar L sigma gamma ell state.2) = 0 :=
    congrArg (fun source : SmoothCapSource L sigma gamma ell => source.2.2) rows
  have scalarRotation := smoothMode_rotation admissible (2 * sign) (apSmoothScalar L sigma gamma ell state.2) raw.2.2
  have scalarZero : apSmoothScalar L sigma gamma ell state.2 = 0 :=
    (smul_eq_zero.mp (scalarRotation.symm.trans thirdZero)).resolve_left
      (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (show 2 * sign ≠ 0 by omega)))
  have negativeMode := rawState_smoothSpin admissible (2 * sign) (-sign) (by omega) state raw
  have negativeRotation := smoothMode_rotation admissible (2 * sign + -sign) _ negativeMode
  have negativeRow := (smoothSpin_force_mode admissible (2 * sign) (-sign) (by omega) state negativeRotation).symm.trans
    ((congrArg (smoothSpin L sigma gamma ell (-sign)) forceZero).trans (map_zero _))
  have thetaDerivative : smoothSignedDerivative admissible 1 sign state.1 = 0 := by
    simpa only [neg_neg] using negative_force_zero sign signed _ _ negativeRow
  have thetaZero := smoothSecondMode_zero admissible sign signed state.1 raw.1 thetaDerivative
  have positiveMode := rawState_smoothSpin admissible (2 * sign) sign signed state raw
  have positiveRotation := smoothMode_rotation admissible (2 * sign + sign) _ positiveMode
  have positiveRow := (smoothSpin_force_mode admissible (2 * sign) sign signed state positiveRotation).symm.trans
    ((congrArg (smoothSpin L sigma gamma ell sign) forceZero).trans (map_zero _))
  have firstZero : smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2) = 0 :=
    positive_force_zero sign signed _ _ ((congrArg (smoothSignedDerivative admissible 1 (-sign)) thetaZero).trans (map_zero _)) positiveRow
  have total : compensatedReconstruct admissible state = state.2 :=
    (congrArg (fun theta : APSmooth L sigma gamma ell 1 => apSmoothCovariant admissible theta + state.2) thetaZero).trans
      ((congrArg (fun value : APSmooth L sigma gamma ell 3 => value + state.2) (map_zero (apSmoothCovariant admissible))).trans (zero_add _))
  have determinantZero : circularDeterminant admissible state = 0 :=
    congrArg (fun source : SmoothCapSource L sigma gamma ell => source.2.1) rows
  have projectedDivZero : -apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible state.2) = 0 :=
    (congrArg (fun value : APSmooth L sigma gamma ell 3 => -apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible value)) total).symm.trans determinantZero
  have meanFixed := removeMean_of_meanZero admissible (apSmoothDiv admissible state.2)
    (smoothMode_meanZero admissible (2 * sign) (by omega) _ (rawState_divergenceMode admissible (2 * sign) sign signed state raw))
  have divZero : apSmoothDiv admissible state.2 = 0 :=
    neg_eq_zero.mp ((congrArg (fun value : APSmooth L sigma gamma ell 1 => -value) meanFixed).symm.trans projectedDivZero)
  have freeDerivative := divergence_free_zero (smoothSignedDerivative admissible 1 sign)
    (smoothSignedDerivative admissible 1 (-sign)) (apSmoothAxial L sigma gamma ell 1)
    (smoothSpin L sigma gamma ell sign (apSmoothPlanar L sigma gamma ell state.2))
    (smoothSpin L sigma gamma ell (-sign) (apSmoothPlanar L sigma gamma ell state.2))
    (apSmoothScalar L sigma gamma ell state.2) firstZero scalarZero
    ((smoothDiv_spins admissible sign signed state.2).symm.trans divZero)
  have flat := ((mem_compensatedFlatCore admissible state).mp domain.1).2
  have storedFlat := (congrArg (APSmoothAxisFirstJetZero admissible) total).mp flat
  have freeFlat := apSmoothValueMap_preserves_firstJet admissible (spinValue ((-sign : ℤ) : ℂ)) _
    (apSmoothValueMap_preserves_firstJet admissible planarPartMap state.2 storedFlat)
  have freePure : HasSmoothMode admissible sign (smoothSpin L sigma gamma ell (-sign) (apSmoothPlanar L sigma gamma ell state.2)) := by
    simpa only [show 2 * sign + -sign = sign by omega] using negativeMode
  have secondZero := smoothPinnedFirstMode_zero admissible sign signed _ freePure freeFlat freeDerivative
  have vectorZero : apSmoothPlanar L sigma gamma ell state.2 = 0 :=
    smoothSpin_ext admissible sign signed (firstZero.trans (map_zero (smoothSpin L sigma gamma ell sign)).symm)
      (secondZero.trans (map_zero (smoothSpin L sigma gamma ell (-sign))).symm)
  have first := (congrArg (apSmoothValueMap L sigma gamma ell planarInclusionMap) vectorZero).trans (map_zero _)
  have second := (congrArg (apSmoothValueMap L sigma gamma ell toroidalInclusionMap) scalarZero).trans (map_zero _)
  have remainderZero := (apSmooth_splitting admissible state.2).symm.trans
    ((congrArg₂ (fun first second : APSmooth L sigma gamma ell 3 => first + second) first second).trans (zero_add _))
  exact Prod.ext thetaZero remainderZero

/-- Genuine uniqueness for arbitrary actual raw exceptional states, with the same original interior rows. -/
theorem exceptionalState_sameRows_unique (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (first second : CompensatedData L sigma gamma ell)
    (firstDomain : first ∈ circularCompensatedCore admissible) (secondDomain : second ∈ circularCompensatedCore admissible)
    (firstRaw : IsRawStateSector admissible (2 * sign) first) (secondRaw : IsRawStateSector admissible (2 * sign) second)
    (sameRows : circularRows admissible first = circularRows admissible second) : first = second := by
  apply sub_eq_zero.mp
  apply exceptionalKernel_zero admissible sign signed (first - second)
    ((circularCompensatedCore admissible).sub_mem firstDomain secondDomain)
    (rawState_sub admissible (2 * sign) first second firstRaw secondRaw)
  exact ((circularRows admissible).map_sub first second).trans
    ((congrArg (fun value : SmoothCapSource L sigma gamma ell => value - circularRows admissible second) sameRows).trans (sub_self _))

end Grad.ActualExceptionalInverse
