import AAT2EnergyDiagonal

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.AnnularReconstruction Grad.ClosedJets Grad.CircularHighWeak Grad.SourceCollarDivision

section Coordinates
variable (lower length : ℝ) (positive : 0 < lower)
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant)

theorem annularEnergyDerivative_diagonal (field : annularEnergySpace lower length positive) :
    annularEnergyDerivative lower length positive
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded (annularEnergyDerivative lower length positive field) := by
  apply lp.ext
  funext mode
  change annularModeDerivative lower
    ((annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field).val mode) =
      (coefficient mode : ℂ) • annularModeDerivative lower (field.val mode)
  rw [annularEnergyDiagonal_apply, map_smul]

theorem annularEnergyMass_diagonal (field : annularEnergySpace lower length positive) :
    annularEnergyMass lower length positive
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded (annularEnergyMass lower length positive field) := by
  apply lp.ext
  funext mode
  change annularModeMass lower
    ((annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field).val mode) =
      (coefficient mode : ℂ) • annularModeMass lower (field.val mode)
  rw [annularEnergyDiagonal_apply, map_smul]

theorem annularEnergyOuter_diagonal (field : annularEnergySpace lower length positive) :
    annularEnergyOuter lower length positive
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded (annularEnergyOuter lower length positive field) := by
  apply lp.ext
  funext mode
  change annularModeOuter lower
    ((annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field).val mode) =
      (coefficient mode : ℂ) • annularModeOuter lower (field.val mode)
  rw [annularEnergyDiagonal_apply, map_smul]

theorem annularMassFamily_diagonal
    (family : HighAnnularMode → RadialL2 1 lower →L[ℂ] RadialL2 1 lower)
    (familyConstant : ℝ) (familyNonnegative : 0 ≤ familyConstant)
    (familyBound : ∀ mode value, ‖family mode value‖ ≤ familyConstant * ‖value‖)
    (field : annularEnergySpace lower length positive) :
    complexLpTwoMap family familyConstant familyNonnegative familyBound
      (annularEnergyMass lower length positive
        (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field)) =
      realLpDiagonal coefficient constant nonnegative bounded
        (complexLpTwoMap family familyConstant familyNonnegative familyBound
          (annularEnergyMass lower length positive field)) := by
  rw [annularEnergyMass_diagonal]
  exact (realLpDiagonal_commutes coefficient constant nonnegative bounded family familyConstant
    familyNonnegative familyBound (annularEnergyMass lower length positive field)).symm

theorem annularEnergyPhase_diagonal (parameters : Grad.CartesianState.PhaseParameters)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (field : annularEnergySpace lower length positive) :
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded
          (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) :=
  annularMassFamily_diagonal lower length positive coefficient constant nonnegative bounded
    (annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength)
    (1 / 2) (by norm_num)
    (annularPhaseMassMap_bound parameters lower length positive lengthPositive widthHalf widthLength) field

theorem annularEnergyValue_diagonal (field : annularEnergySpace lower length positive) :
    annularEnergyValue lower length positive
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded (annularEnergyValue lower length positive field) :=
  annularMassFamily_diagonal lower length positive coefficient constant nonnegative bounded
    (annularValueMassMap lower length positive) (1 / 3) (by norm_num)
    (annularValueMassMap_bound lower length positive) field

theorem annularEnergyRadial_diagonal (field : annularEnergySpace lower length positive) :
    annularEnergyRadial lower length positive
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded (annularEnergyRadial lower length positive field) :=
  annularMassFamily_diagonal lower length positive coefficient constant nonnegative bounded
    (annularRadialMassMap lower length positive) (2 / 3) (by norm_num)
    (annularRadialMassMap_bound lower length positive) field

theorem annularEnergyD_diagonal (field : annularEnergySpace lower length positive) :
    annularEnergyD lower length positive
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded (annularEnergyD lower length positive field) :=
  annularMassFamily_diagonal lower length positive coefficient constant nonnegative bounded
    (fun mode => annularImaginarySymbolMap lower length positive mode
      ((mode.val.1 : ℝ) * highMultiplier mode.val.1) (annularDSymbol_dominated lower length positive mode))
    1 (by norm_num) (fun mode => annularImaginarySymbolMap_bound lower length positive mode _ _) field

theorem annularEnergyCell_diagonal (field : annularEnergySpace lower length positive) :
    annularEnergyCell lower length positive
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded (annularEnergyCell lower length positive field) :=
  annularMassFamily_diagonal lower length positive coefficient constant nonnegative bounded
    (fun mode => annularImaginarySymbolMap lower length positive mode
      (highMultiplier mode.val.1 * (mode.val.2 : ℝ) / length) (annularCellSymbol_dominated lower length positive mode))
    1 (by norm_num) (fun mode => annularImaginarySymbolMap_bound lower length positive mode _ _) field

end Coordinates

end Grad.AnnularGrades
