import ASX11SpinReconstruction
import GQF18CircularSourceJets

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.ActualCenterVolterra Grad.NonlinearQuotientBounds Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.Compensated
open Grad.NonlinearDivision (closedOrigin)

/-- The nonzero mode has an actual zero value at the axis. -/
theorem pureMode_origin_zero {dimension : ℕ} (mode : ℤ) (nonzero : mode ≠ 0)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) : field.value closedOrigin = 0 := by
  have value := congrArg (fun jet : ClosedJet dimension => jet.value closedOrigin) (pureMode_rotation mode field pure)
  have vanishing : (Complex.I * (mode : ℂ)) • field.value closedOrigin = 0 :=
    value.symm.trans (rotationJet_origin_zero field)
  exact (smul_eq_zero.mp vanishing).resolve_left (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr nonzero))

private theorem rotation_eigen_axes {E : Type*} [AddCommGroup E] [Module ℂ E]
    (coefficient : ℂ) (nonzero : coefficient * coefficient + 1 ≠ 0)
    (first second : E) (firstEquation : second = coefficient • first)
    (secondEquation : -first = coefficient • second) : first = 0 ∧ second = 0 := by
  have zero : (coefficient * coefficient + 1) • first = 0 := by
    rw [add_smul, mul_smul, one_smul, ← firstEquation, ← secondEquation, neg_add_cancel]
  have firstZero := (smul_eq_zero.mp zero).resolve_left nonzero
  exact ⟨firstZero, firstEquation.trans (by rw [firstZero, smul_zero])⟩

theorem rotationEigen_coefficient_nonzero (mode : ℤ) (notPositive : mode ≠ 1) (notNegative : mode ≠ -1) :
    (Complex.I * (mode : ℂ)) * (Complex.I * (mode : ℂ)) + 1 ≠ 0 := by
  have positive : (mode : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast notPositive)
  have negative : (mode : ℂ) + 1 ≠ 0 := by
    intro zero
    apply notNegative
    have cast : (mode : ℂ) = -1 := by linear_combination zero
    exact_mod_cast cast
  have formula : (Complex.I * (mode : ℂ)) * (Complex.I * (mode : ℂ)) + 1 =
      -((mode : ℂ) - 1) * ((mode : ℂ) + 1) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [formula]
  exact mul_ne_zero (neg_ne_zero.mpr positive) negative

/-- Modes outside 0 and ±1 have a literal zero first Cartesian jet. -/
theorem pureMode_pinned {dimension : ℕ} (mode : ℤ) (nonzero : mode ≠ 0)
    (notPositive : mode ≠ 1) (notNegative : mode ≠ -1)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) : CenterPinned field := by
  refine ⟨pureMode_origin_zero mode nonzero field pure, ?_⟩
  have rotation := pureMode_rotation mode field pure
  have derivative (direction : Fin 2) := congrArg
    (fun jet : ClosedJet dimension => (Grad.NonlinearQuotientBounds.partialJet direction jet).value closedOrigin) rotation
  have axisZero : (Grad.NonlinearQuotientBounds.partialJet 0 (rotationJet field)).value closedOrigin =
      (Grad.NonlinearQuotientBounds.partialJet 1 field).value closedOrigin := by
    simpa [originalPartial_eq, spatialBasis] using
      partialJet_rotation_origin field 0
  have axisOne : (Grad.NonlinearQuotientBounds.partialJet 1 (rotationJet field)).value closedOrigin =
      -(Grad.NonlinearQuotientBounds.partialJet 0 field).value closedOrigin := by
    simpa [originalPartial_eq, spatialBasis] using
      partialJet_rotation_origin field 1
  have firstEquation := axisZero.symm.trans (derivative 0)
  have secondEquation := axisOne.symm.trans (derivative 1)
  simp only [centerPartial_smul, closedJet_value_smul, ContinuousMap.smul_apply] at firstEquation secondEquation
  have axes := rotation_eigen_axes (Complex.I * (mode : ℂ))
    (rotationEigen_coefficient_nonzero mode notPositive notNegative)
    ((Grad.NonlinearQuotientBounds.partialJet 0 field).value closedOrigin)
    ((Grad.NonlinearQuotientBounds.partialJet 1 field).value closedOrigin) firstEquation secondEquation
  intro direction
  fin_cases direction
  · exact axes.1
  · exact axes.2

theorem pureMode_mean_zero {dimension : ℕ} (mode : ℤ) (nonzero : mode ≠ 0)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) : angularClosedJet 0 field = 0 := by
  have projection := angularClosedJet_projection 0 mode field
  rw [pure, if_neg (Ne.symm nonzero)] at projection
  exact projection

end Grad.ActualExceptionalInverse
