import AIA7ActualCircularOutputCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighWeak Grad.CircularHighRegularity

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

theorem decodedValue_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    annularEnergyValue lower L positive (bEnergyDecode lower L positive field) mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) • annularEnergyValue lower L positive field mode :=
  congrArg (fun value : AnnularBulk lower => value mode)
    (annularEnergyValue_diagonal lower L positive (fun mode => Real.sqrt (highMultiplier mode.val.1))
      1 (by norm_num) bEnergyDecode_bound field)

theorem decodedDerivative_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    annularEnergyDerivative lower L positive (bEnergyDecode lower L positive field) mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) • annularEnergyDerivative lower L positive field mode :=
  congrArg (fun value : AnnularBulk lower => value mode)
    (annularEnergyDerivative_diagonal lower L positive (fun mode => Real.sqrt (highMultiplier mode.val.1))
      1 (by norm_num) bEnergyDecode_bound field)

theorem decodedPhase_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength (bEnergyDecode lower L positive field) mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) •
        annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field mode := by
  rw [annularTiltEnergyPhase_mode, decodedValue_mode, map_smul, annularTiltEnergyPhase_mode]

theorem decodedRadius_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    highEnergyRadius lower L positive (bEnergyDecode lower L positive field) mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) • highEnergyRadius lower L positive field mode := by
  rw [highEnergyRadius_mode, decodedValue_mode, map_smul, highEnergyRadius_mode]

theorem decodedAngularRadius_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) • highEnergyAngularRadius lower L positive field mode := by
  rw [highEnergyAngularRadius_mode, decodedRadius_mode, highEnergyAngularRadius_mode, smul_comm]

theorem decodedCell_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    highEnergyCell lower L positive (bEnergyDecode lower L positive field) mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) • highEnergyCell lower L positive field mode := by
  rw [highEnergyCell_mode, decodedValue_mode, highEnergyCell_mode, smul_comm]

theorem highPhysicalDerivative_decoded_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) •
        (annularEnergyDerivative lower L positive field mode -
          annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field mode) := by
  change annularEnergyDerivative lower L positive (bEnergyDecode lower L positive field) mode -
    annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength (bEnergyDecode lower L positive field) mode = _
  rw [decodedDerivative_mode, decodedPhase_mode, smul_sub]

theorem highPhysicalTestDerivative_decoded_mode (field : annularEnergySpace lower L positive) (mode : HighAnnularMode) :
    highPhysicalTestDerivative parameters lower L positive lengthPositive widthHalf widthLength field mode =
      (Real.sqrt (highMultiplier mode.val.1) : ℂ) •
        (annularEnergyDerivative lower L positive field mode +
          annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field mode) := by
  change annularEnergyDerivative lower L positive (bEnergyDecode lower L positive field) mode +
    annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength (bEnergyDecode lower L positive field) mode = _
  rw [decodedDerivative_mode, decodedPhase_mode, smul_add]

end Grad.AnnularCircularForm
