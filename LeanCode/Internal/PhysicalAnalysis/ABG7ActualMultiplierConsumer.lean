import ABG6RadialMultiplierCommutation

noncomputable section
namespace Grad.OrdinaryDiskMultiplier
open Grad.CartesianState Grad.CircularHighWeak Grad.OrdinaryDiskCalculus
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.InteriorLocalization Grad.InteriorPeriodization
attribute [local instance] unitNormedSpace

/-- Unconditional all-grade T4 consumer for the same actual disk L2 field. -/
theorem actualDiskMultiplier_consumer (grade : ℕ) (field : unitDiskSobolev grade) :
    ∃ image : unitDiskSobolev grade,
      unitDiskBulk grade image = diskB (unitDiskBulk grade field) ∧
      ‖image‖ ≤ unitBConstant grade * ‖field‖ :=
  ⟨unitB grade field, unitB_bulk grade field, unitB_bound grade field⟩

/-- The existing interior cutoff acts after B, with its literal bulk and
ordinary grade bound. This uses no rotational-invariance claim about that cutoff. -/
theorem actualInteriorB_consumer (grade : ℕ) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (unitScalar grade interiorCutoff.toFun interiorCutoff.smooth (unitB grade field)) =
      diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskB (unitDiskBulk grade field)) ∧
    ‖unitScalar grade interiorCutoff.toFun interiorCutoff.smooth (unitB grade field)‖ ≤
      (unitProductConstant grade (apScalarOperatorJet 1 interiorCutoff.toFun interiorCutoff.smooth) *
        unitBConstant grade) * ‖field‖ := by
  constructor
  · exact (unitScalar_bulk grade _ _ _).trans (congrArg (diskScalar _ _) (unitB_bulk grade field))
  · exact (unitScalar_bound grade _ _ _).trans
      ((mul_le_mul_of_nonneg_left (unitB_bound grade field) (unitProductConstant_nonnegative grade _)).trans_eq
        (mul_assoc _ _ _).symm)

/-- The fixed periodization cutoff also has its literal composition estimate;
no commutation with the choice-defined bump function is assumed. -/
theorem actualPeriodizationB_consumer (grade : ℕ) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (unitScalar grade periodizationCutoff.toFun periodizationCutoff.smooth (unitB grade field)) =
      diskScalar periodizationCutoff.toFun periodizationCutoff.smooth (diskB (unitDiskBulk grade field)) ∧
    ‖unitScalar grade periodizationCutoff.toFun periodizationCutoff.smooth (unitB grade field)‖ ≤
      (unitProductConstant grade (apScalarOperatorJet 1 periodizationCutoff.toFun periodizationCutoff.smooth) *
        unitBConstant grade) * ‖field‖ := by
  constructor
  · exact (unitScalar_bulk grade _ _ _).trans (congrArg (diskScalar _ _) (unitB_bulk grade field))
  · exact (unitScalar_bound grade _ _ _).trans
      ((mul_le_mul_of_nonneg_left (unitB_bound grade field) (unitProductConstant_nonnegative grade _)).trans_eq
        (mul_assoc _ _ _).symm)

end Grad.OrdinaryDiskMultiplier
