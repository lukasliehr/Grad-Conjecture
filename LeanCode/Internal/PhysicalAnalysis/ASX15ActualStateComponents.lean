import ASX14SmoothSpinIdentities

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
variable {L sigma gamma ell : ℝ}

def smoothStoredPair (L sigma gamma ell : ℝ) (vector : APSmooth L sigma gamma ell 2)
    (scalar : APSmooth L sigma gamma ell 1) : APSmooth L sigma gamma ell 3 :=
  apSmoothValueMap L sigma gamma ell planarInclusionMap vector +
    apSmoothValueMap L sigma gamma ell toroidalInclusionMap scalar

theorem smoothStoredPair_planar (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (scalar : APSmooth L sigma gamma ell 1) :
    apSmoothPlanar L sigma gamma ell (smoothStoredPair L sigma gamma ell vector scalar) = vector := by
  have first := (smoothValueMap_comp admissible planarInclusionMap planarPartMap vector).trans
    ((congrArg (fun mapping => apSmoothValueMap L sigma gamma ell mapping vector) planarPart_planarInclusion).trans
      (smoothValueMap_identity admissible vector))
  have second := (smoothValueMap_comp admissible toroidalInclusionMap planarPartMap scalar).trans
    ((congrArg (fun mapping => apSmoothValueMap L sigma gamma ell mapping scalar) planarPart_toroidalInclusion).trans
      (smoothValueMap_zero admissible scalar))
  exact ((apSmoothPlanar L sigma gamma ell).map_add
    (apSmoothValueMap L sigma gamma ell planarInclusionMap vector)
    (apSmoothValueMap L sigma gamma ell toroidalInclusionMap scalar)).trans
      ((congrArg₂ (fun a b : APSmooth L sigma gamma ell 2 => a + b) first second).trans (add_zero vector))

theorem smoothStoredPair_scalar (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (scalar : APSmooth L sigma gamma ell 1) :
    apSmoothScalar L sigma gamma ell (smoothStoredPair L sigma gamma ell vector scalar) = scalar := by
  have first := (smoothValueMap_comp admissible planarInclusionMap toroidalPartMap vector).trans
    ((congrArg (fun mapping => apSmoothValueMap L sigma gamma ell mapping vector) toroidalPart_planarInclusion).trans
      (smoothValueMap_zero admissible vector))
  have second := (smoothValueMap_comp admissible toroidalInclusionMap toroidalPartMap scalar).trans
    ((congrArg (fun mapping => apSmoothValueMap L sigma gamma ell mapping scalar) toroidalPart_toroidalInclusion).trans
      (smoothValueMap_identity admissible scalar))
  exact ((apSmoothScalar L sigma gamma ell).map_add
    (apSmoothValueMap L sigma gamma ell planarInclusionMap vector)
    (apSmoothValueMap L sigma gamma ell toroidalInclusionMap scalar)).trans
      ((congrArg₂ (fun a b : APSmooth L sigma gamma ell 1 => a + b) first second).trans (zero_add scalar))

theorem exceptionalCovariant_planar (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) :
    apSmoothPlanar L sigma gamma ell (exceptionalCovariant admissible sign source) = exceptionalPlanar admissible sign source :=
  smoothStoredPair_planar admissible (exceptionalPlanar admissible sign source) (exceptionalToroidal admissible sign source)

theorem exceptionalCovariant_scalar (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) :
    apSmoothScalar L sigma gamma ell (exceptionalCovariant admissible sign source) = exceptionalToroidal admissible sign source :=
  smoothStoredPair_scalar admissible (exceptionalPlanar admissible sign source) (exceptionalToroidal admissible sign source)

theorem smoothCovariant_planar (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 1) :
    apSmoothPlanar L sigma gamma ell (apSmoothCovariant admissible field) = apSmoothGradient admissible field :=
  smoothStoredPair_planar admissible (apSmoothGradient admissible field) (apSmoothAxial L sigma gamma ell 1 field)

theorem smoothCovariant_scalar (admissible : Admissible L sigma gamma ell) (field : APSmooth L sigma gamma ell 1) :
    apSmoothScalar L sigma gamma ell (apSmoothCovariant admissible field) = apSmoothAxial L sigma gamma ell 1 field :=
  smoothStoredPair_scalar admissible (apSmoothGradient admissible field) (apSmoothAxial L sigma gamma ell 1 field)

theorem exceptionalState_planar (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) :
    apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2 =
      exceptionalPlanar admissible sign source - apSmoothGradient admissible (exceptionalTheta admissible sign source) :=
  ((apSmoothPlanar L sigma gamma ell).map_sub (exceptionalCovariant admissible sign source)
    (apSmoothCovariant admissible (exceptionalTheta admissible sign source))).trans
      (congrArg₂ (fun a b : APSmooth L sigma gamma ell 2 => a - b)
        (exceptionalCovariant_planar admissible sign source)
        (smoothCovariant_planar admissible (exceptionalTheta admissible sign source)))

private theorem axial_cancellation {E : Type*} [AddCommGroup E] [Module ℂ E]
    (axial : E →ₗ[ℂ] E) (coefficient : ℂ) (source potential : E) :
    coefficient • (source + axial potential) - axial (coefficient • potential) = coefficient • source := by
  rw [map_smul, smul_add, add_sub_cancel_right]

/-- The original stored scalar e is exactly H_c/(2 i sigma), after the
actual scaled axial derivative in b cancels the one in the covariant gradient. -/
theorem exceptionalState_scalar (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) :
    apSmoothScalar L sigma gamma ell (exceptionalState admissible sign source).2 =
      (2 * Complex.I * (sign : ℂ))⁻¹ • source.2.2 := by
  have components := ((apSmoothScalar L sigma gamma ell).map_sub (exceptionalCovariant admissible sign source)
    (apSmoothCovariant admissible (exceptionalTheta admissible sign source))).trans
      (congrArg₂ (fun a b : APSmooth L sigma gamma ell 1 => a - b)
        (exceptionalCovariant_scalar admissible sign source)
        (smoothCovariant_scalar admissible (exceptionalTheta admissible sign source)))
  exact components.trans (axial_cancellation (apSmoothAxial L sigma gamma ell 1)
    (2 * Complex.I * (sign : ℂ))⁻¹ source.2.2 (exceptionalPsi admissible sign source))

theorem exceptionalPlanar_first (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell) :
    smoothSpin L sigma gamma ell sign (exceptionalPlanar admissible sign source) = exceptionalFixedSpin admissible sign source :=
  smoothSpin_planar_first admissible sign signed _ _

theorem exceptionalPlanar_second (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell) :
    smoothSpin L sigma gamma ell (-sign) (exceptionalPlanar admissible sign source) = exceptionalFreeSpin admissible sign source :=
  smoothSpin_planar_second admissible sign signed _ _

end Grad.ActualExceptionalInverse
