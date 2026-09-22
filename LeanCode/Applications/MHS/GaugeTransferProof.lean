import GaugeTransferInterface

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

/-- The actual N16–N19 seed-slice transfer theorem. -/
theorem actualSeedTransfer : SeedTransferGoal := by
  intro phase
  refine ⟨fun parameterM insideM parameterN insideN =>
    seedTransfer phase parameterM insideM parameterN insideN, ?_, ?_, ?_, ?_⟩
  · intro parameterM insideM parameterN insideN
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro field
      rw [seedTransfer_planar_part, planarTransfer_apply]
    · intro field
      rw [seedTransfer_toroidal_part, seedTransfer_planar_part]
      rfl
    · exact seedTransfer_poloidal_gauge phase parameterM insideM parameterN insideN
    · exact seedTransfer_toroidal_gauge phase parameterM insideM parameterN insideN
    · refine ⟨seedTransferGradeConstant phase parameterM parameterN, ?_, ?_⟩
      · intro grade
        unfold seedTransferGradeConstant
        have first := planarTransferGradeConstant_nonneg phase parameterM parameterN grade
        have second := orthogonalGradeConstant_nonnegative grade
        have third := coordinateRowConstant_nonneg grade
        have fourth := multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le
        have fifth := envelope_nonneg phase grade (derivativeRowCoefficients parameterN 0)
        have sixth := envelope_nonneg phase grade (derivativeRowCoefficients parameterN 1)
        have seventh := norm_nonneg (phase.length⁻¹ : ℂ)
        positivity
      · intro grade field
        rw [ofCoreLinear_norm_coordinates, ofCoreLinear_norm_coordinates]
        exact seedTransfer_coordinates_bound phase parameterM insideM parameterN insideN field
    · exact seedTransfer_zero_first_jets phase parameterM insideM parameterN insideN
    · exact seedTransfer_radial phase parameterM insideM parameterN insideN
  · intro parameterM insideM parameterN insideN field poloidalZero toroidalZero
    exact seedTransfer_reverse phase parameterM insideM parameterN insideN field
      poloidalZero toroidalZero
  · intro parameterM insideM parameterN insideN parameterP insideP field
    exact seedTransfer_cocycle phase parameterM insideM parameterN insideN
      parameterP insideP field
  · intro parameterM insideM field poloidalZero toroidalZero
    exact seedTransfer_identity phase parameterM insideM field poloidalZero toroidalZero

end Grad.Constraints.Gauges
