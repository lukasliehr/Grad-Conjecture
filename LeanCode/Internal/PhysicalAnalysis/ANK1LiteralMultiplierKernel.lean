import ANT6ActualClosedDiskConsumer
import ANV13ReconstructionConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarResidual
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.ActualAngularInverse Grad.CartesianScalarElimination

/-- The actual ANS formula, including its nonzero constant-mode coefficient. -/
theorem literalMultiplier_coefficient (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (field + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 field)) =
      if mode = 0 then angularClosedJet 0 field else
        (1 - 4 / (mode : ℂ) ^ 2) • angularClosedJet mode field := by
  by_cases nonzero : mode = 0
  · subst mode
    rw [angularClosedJet_add, angularClosedJet_smul, shiftInverseJet_coefficient]
    simp
  · rw [if_neg nonzero, angularClosedJet_add, angularClosedJet_smul,
      shiftInverseJet_coefficient, shiftInverseJet_coefficient]
    simp only [neg_zero, add_zero, if_neg nonzero, smul_smul]
    have algebra : (1 : ℂ) + 4 * ((Complex.I * (mode : ℂ))⁻¹ * (Complex.I * (mode : ℂ))⁻¹) =
        1 - 4 / (mode : ℂ) ^ 2 := by
      have frequency : (mode : ℂ) ≠ 0 := by exact_mod_cast nonzero
      field_simp
      simp [Complex.I_sq]
      ring
    calc
      _ = (1 + 4 * ((Complex.I * (mode : ℂ))⁻¹ * (Complex.I * (mode : ℂ))⁻¹)) •
          angularClosedJet mode field := by rw [add_smul, one_smul]
      _ = _ := congrArg (fun scalar : ℂ => scalar • angularClosedJet mode field) algebra

theorem literalMultiplier_coefficient_ne_zero (mode : ℤ) (nonzero : mode ≠ 0)
    (positive : mode ≠ 2) (negative : mode ≠ -2) : (1 : ℂ) - 4 / (mode : ℂ) ^ 2 ≠ 0 := by
  intro vanishes
  have frequency : (mode : ℂ) ≠ 0 := by exact_mod_cast nonzero
  have square : (mode : ℂ) ^ 2 = 4 := by
    have identity := (eq_div_iff (pow_ne_zero 2 frequency)).mp (sub_eq_zero.mp vanishes)
    simpa only [one_mul] using identity
  have factored : ((mode : ℂ) - 2) * ((mode : ℂ) + 2) = 0 := by
    calc
      _ = (mode : ℂ) ^ 2 - 4 := by ring
      _ = 0 := by rw [square]; norm_num
  rcases mul_eq_zero.mp factored with first | second
  · apply positive
    exact_mod_cast sub_eq_zero.mp first
  · apply negative
    have equality : (mode : ℂ) = -2 := (eq_neg_iff_add_eq_zero).mpr second
    exact_mod_cast equality

theorem literalMultiplier_kernel_mode (field : ClosedJet 1)
    (kernel : field + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 field) = 0)
    (mode : ℤ) (positive : mode ≠ 2) (negative : mode ≠ -2) : angularClosedJet mode field = 0 := by
  have coefficient := (literalMultiplier_coefficient mode field).symm.trans
    ((congrArg (angularClosedJet mode) kernel).trans (map_zero (angularClosedJetLinear 1 mode)))
  by_cases zero : mode = 0
  · subst mode
    simpa using coefficient
  · rw [if_neg zero] at coefficient
    exact (smul_eq_zero.mp coefficient).resolve_left (literalMultiplier_coefficient_ne_zero mode zero positive negative)

/-- The full multiplier has kernel exactly the two resonant angular modes.
In particular the mean and the center modes are not in its kernel. -/
theorem literalMultiplier_kernel_iff (field : ClosedJet 1) :
    field + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 field) = 0 ↔
      field = angularClosedJet 2 field + angularClosedJet (-2) field := by
  constructor
  · intro kernel
    apply scalarJet_angular_ext
    intro mode
    rw [angularClosedJet_add, angularClosedJet_projection, angularClosedJet_projection]
    by_cases positive : mode = 2
    · subst mode
      simp
    · by_cases negative : mode = -2
      · subst mode
        simp
      · rw [if_neg positive, if_neg negative, zero_add]
        exact literalMultiplier_kernel_mode field kernel mode positive negative
  · intro supported
    apply scalarJet_angular_ext
    intro mode
    rw [literalMultiplier_coefficient, show angularClosedJet mode (0 : ClosedJet 1) = 0 from map_zero (angularClosedJetLinear 1 mode)]
    by_cases positive : mode = 2
    · subst mode
      norm_num
    · by_cases negative : mode = -2
      · subst mode
        norm_num
      · have absent := congrArg (angularClosedJet mode) supported
        rw [angularClosedJet_add, angularClosedJet_projection, angularClosedJet_projection,
          if_neg positive, if_neg negative, zero_add] at absent
        by_cases zero : mode = 0
        · subst mode
          simpa using absent
        · rw [if_neg zero, absent, smul_zero]

theorem literalMultiplier_eq_zero (field : ClosedJet 1)
    (positive : angularClosedJet 2 field = 0) (negative : angularClosedJet (-2) field = 0)
    (kernel : field + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 field) = 0) : field = 0 := by
  rw [(literalMultiplier_kernel_iff field).mp kernel, positive, negative, zero_add]

end Grad.ActualScalarResidual
