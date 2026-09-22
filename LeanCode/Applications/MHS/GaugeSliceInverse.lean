import GaugeSliceTransfer

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

variable (phase : PhaseParameters)
variable (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
variable (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain)
variable (parameterP : Seed.Parameters) (insideP : parameterP ∈ Seed.parameterDomain)

/-- Extraction of the literal poloidal gauge from the correction equation. -/
theorem poloidal_gauge_extraction (field : ACore phase 3)
    (poloidalZero : poloidalCorrection phase parameterM insideM field = 0) :
    tangentialCore phase (seedTransposeCore phase parameterM insideM
      (planarPartCore phase field)) = 0 := by
  have planarZero := congrArg (planarPartCore phase) poloidalZero
  rw [poloidalCorrection_apply, planarPartCore_planarInclusionCore, map_zero] at planarZero
  have inverted := congrArg (seedInverseCore phase parameterM insideM) planarZero
  rw [seedInverse_seedMatrix_core phase parameterM insideM, map_zero] at inverted
  exact inverted

/-- Extraction of the literal toroidal gauge from the correction equation. -/
theorem toroidal_gauge_extraction (field : ACore phase 3)
    (toroidalZero : toroidalCorrection phase parameterM insideM field = 0) :
    angularCore phase 0 (toroidalPartCore phase field) +
      (phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterM insideM
        (planarPartCore phase field)) = 0 := by
  have extracted := congrArg (toroidalPartCore phase) toroidalZero
  rw [toroidalCorrection_apply, toroidalPartCore_toroidalInclusionCore, map_zero] at extracted
  rw [← extracted, map_add, map_smul]

/-- The reverse planar transfer is the exact inverse on the poloidal gauge
kernel. -/
theorem planarTransfer_reverse (field : ACore phase 3)
    (poloidalZero : poloidalCorrection phase parameterM insideM field = 0) :
    planarTransfer phase parameterN insideN parameterM insideM
        (planarTransfer phase parameterM insideM parameterN insideN
          (planarPartCore phase field)) =
      planarPartCore phase field := by
  rw [planarTransfer_apply, planarTransfer_apply,
    seedInverse_seedMatrix_core phase parameterN insideN,
    sliceProjection_absorb phase parameterM insideM parameterN insideN,
    sliceProjection_apply, gaugeComposite_apply,
    seedMatrix_seedInverse_core phase parameterM insideM,
    poloidal_gauge_extraction phase parameterM insideM field poloidalZero,
    sub_zero, seedMatrix_seedInverse_core phase parameterM insideM]

/-- The literal N18 reverse transfer is the exact two-sided inverse on the
intersection of the two source gauge kernels. -/
theorem seedTransfer_reverse (field : ACore phase 3)
    (poloidalZero : poloidalCorrection phase parameterM insideM field = 0)
    (toroidalZero : toroidalCorrection phase parameterM insideM field = 0) :
    seedTransfer phase parameterN insideN parameterM insideM
        (seedTransfer phase parameterM insideM parameterN insideN field) = field := by
  set forward := seedTransfer phase parameterM insideM parameterN insideN field with forward_def
  have planarReverse : planarTransfer phase parameterN insideN parameterM insideM
      (planarPartCore phase forward) = planarPartCore phase field := by
    rw [forward_def, seedTransfer_planar_part]
    exact planarTransfer_reverse phase parameterM insideM parameterN insideN field poloidalZero
  have toroidalReverse : transferToroidalComponent phase parameterN insideN
      parameterM insideM forward = toroidalPartCore phase field := by
    have componentExpand : transferToroidalComponent phase parameterN insideN parameterM
        insideM forward =
        (toroidalPartCore phase forward -
          angularCore phase 0 (toroidalPartCore phase forward)) -
          (phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterM
            insideM (planarTransfer phase parameterN insideN parameterM insideM
              (planarPartCore phase forward))) := rfl
    rw [componentExpand, planarReverse]
    have nonmean := seedTransfer_nonmean phase parameterM insideM parameterN insideN field
    rw [← forward_def] at nonmean
    rw [nonmean]
    have extraction := toroidal_gauge_extraction phase parameterM insideM field toroidalZero
    have meanIdentity : (phase.length⁻¹ : ℂ) • angularCore phase 0
        (derivativeDotCore phase parameterM insideM (planarPartCore phase field)) =
        -angularCore phase 0 (toroidalPartCore phase field) :=
      eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact extraction)
    rw [meanIdentity]
    abel
  calc seedTransfer phase parameterN insideN parameterM insideM forward
      = planarInclusionCore phase (planarTransfer phase parameterN insideN parameterM insideM
          (planarPartCore phase forward)) +
        toroidalInclusionCore phase (transferToroidalComponent phase parameterN insideN
          parameterM insideM forward) := rfl
    _ = planarInclusionCore phase (planarPartCore phase field) +
        toroidalInclusionCore phase (toroidalPartCore phase field) := by
        rw [planarReverse, toroidalReverse]
    _ = field := splittingCore_reconstruction phase field

/-- The exact three-seed cocycle of the literal N18 transfer, with no gauge
hypothesis needed. -/
theorem seedTransfer_cocycle (field : ACore phase 3) :
    seedTransfer phase parameterN insideN parameterP insideP
        (seedTransfer phase parameterM insideM parameterN insideN field) =
      seedTransfer phase parameterM insideM parameterP insideP field := by
  set forward := seedTransfer phase parameterM insideM parameterN insideN field with forward_def
  have planarCocycle : planarTransfer phase parameterN insideN parameterP insideP
      (planarPartCore phase forward) =
      planarTransfer phase parameterM insideM parameterP insideP
        (planarPartCore phase field) := by
    rw [forward_def, seedTransfer_planar_part, planarTransfer_apply, planarTransfer_apply,
      planarTransfer_apply, seedInverse_seedMatrix_core phase parameterN insideN,
      sliceProjection_absorb phase parameterP insideP parameterN insideN]
  have toroidalCocycle : transferToroidalComponent phase parameterN insideN parameterP
      insideP forward =
      transferToroidalComponent phase parameterM insideM parameterP insideP field := by
    have leftExpand : transferToroidalComponent phase parameterN insideN parameterP insideP
        forward =
        (toroidalPartCore phase forward -
          angularCore phase 0 (toroidalPartCore phase forward)) -
          (phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterP
            insideP (planarTransfer phase parameterN insideN parameterP insideP
              (planarPartCore phase forward))) := rfl
    have rightExpand : transferToroidalComponent phase parameterM insideM parameterP insideP
        field =
        (toroidalPartCore phase field -
          angularCore phase 0 (toroidalPartCore phase field)) -
          (phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterP
            insideP (planarTransfer phase parameterM insideM parameterP insideP
              (planarPartCore phase field))) := rfl
    have nonmean := seedTransfer_nonmean phase parameterM insideM parameterN insideN field
    rw [← forward_def] at nonmean
    rw [leftExpand, rightExpand, planarCocycle, nonmean]
  calc seedTransfer phase parameterN insideN parameterP insideP forward
      = planarInclusionCore phase (planarTransfer phase parameterN insideN parameterP insideP
          (planarPartCore phase forward)) +
        toroidalInclusionCore phase (transferToroidalComponent phase parameterN insideN
          parameterP insideP forward) := rfl
    _ = seedTransfer phase parameterM insideM parameterP insideP field := by
        rw [planarCocycle, toroidalCocycle]
        rfl

/-- The identity-seed transfer is the identity on the gauge kernels. -/
theorem seedTransfer_identity (field : ACore phase 3)
    (poloidalZero : poloidalCorrection phase parameterM insideM field = 0)
    (toroidalZero : toroidalCorrection phase parameterM insideM field = 0) :
    seedTransfer phase parameterM insideM parameterM insideM field = field := by
  have viaReverse := seedTransfer_reverse phase parameterM insideM parameterM insideM field
    poloidalZero toroidalZero
  have viaCocycle := seedTransfer_cocycle phase parameterM insideM parameterM insideM
    parameterM insideM field
  calc seedTransfer phase parameterM insideM parameterM insideM field
      = seedTransfer phase parameterM insideM parameterM insideM
          (seedTransfer phase parameterM insideM parameterM insideM field) := viaCocycle.symm
    _ = field := viaReverse

end Grad.Constraints.Gauges
