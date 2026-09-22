import GQ5ActualLedgerProjection

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearDivision

/-- The nonsingular fixed projection vanishes precisely when its two
literal physical moments vanish. The origin is handled without division. -/
theorem cartesianComplement_zero_iff (field : ClosedDisk → PhysicalValue 3)
    (continuous : Continuous field) (point : ClosedDisk) :
    cartesianComplementValue field point = 0 ↔
      closedAngularMean (fun other => storedTangentDot other (field other)) point = 0 ∧
      closedAngularMean (fun other => field other 2) point = 0 := by
  rw [cartesianComplementValue_eq_polar field continuous]
  constructor
  · intro zero
    constructor
    · by_cases axis : point.val = 0
      · have atOrigin : point = closedOrigin := Subtype.ext axis
        rw [atOrigin, closedAngularMean_origin]
        simp [storedTangentDot, closedOrigin]
      · have tangent := congrArg (storedTangentDot point) zero
        change storedTangentDot point (complementProfile _ _ point) = storedTangentDot point 0 at tangent
        rw [storedTangentDot_profile] at tangent
        change radiusScalar point * ((radiusScalar point)⁻¹ *
          closedAngularMean (fun other => storedTangentDot other (field other)) point) = _ at tangent
        rw [← mul_assoc, mul_inv_cancel₀ (radiusScalar_nonzero point axis), one_mul] at tangent
        simpa only [storedTangentDot, PiLp.zero_apply, mul_zero, add_zero] using tangent
    · have third := congrArg (fun value : PhysicalValue 3 => value 2) zero
      change complementProfile _ _ point 2 = 0 at third
      rwa [complementProfile_third] at third
  · rintro ⟨first, second⟩
    unfold fixedComplementValue complementProfile
    dsimp only
    rw [first, second, mul_zero, zero_smul, zero_smul, add_zero]

theorem apGaugeMap_zero_iff_means {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    {grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell 3 grade) :
    apGaugeMap admissible gauge grade field = 0 ↔
      ∀ angle point,
        closedAngularMean (fun other => storedTangentDot other
          (fullGaugeValueAction gauge grade angle (apPhysicalValue admissible large angle field) other)) point = 0 ∧
        closedAngularMean (fun other =>
          fullGaugeValueAction gauge grade angle (apPhysicalValue admissible large angle field) other 2) point = 0 := by
  constructor
  · intro zero angle point
    have physical := congrArg (fun vector => apPhysicalValue admissible large angle vector point) zero
    rw [apGaugeMap_physical admissible gauge coherent large, map_zero] at physical
    change cartesianComplementValue (fullGaugeValueAction gauge grade angle
      (apPhysicalValue admissible large angle field)) point = 0 at physical
    exact (cartesianComplement_zero_iff _ (fullGaugeValueAction_continuous admissible gauge coherent grade angle
      _ (apPhysicalValue admissible large angle field).continuous) point).mp physical
  · intro means
    apply apPhysicalValue_ext admissible large
    intro angle
    rw [apGaugeMap_physical admissible gauge coherent large, map_zero]
    apply ContinuousMap.ext
    intro point
    exact (cartesianComplement_zero_iff _ (fullGaugeValueAction_continuous admissible gauge coherent grade angle
      _ (apPhysicalValue admissible large angle field).continuous) point).mpr (means angle point)

end Grad.GaugeCoefficients.Physical.GaugeTransfer
