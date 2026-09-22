import AveragesInterface

noncomputable section

namespace Grad.Constraints

/-- The complete, original-width Cartesian rotation-projection block N1-N5. -/
theorem averages : AveragesGoal where
  angular_formula := angularClosedJet_value
  angular_projection := angularClosedJet_projection
  angular_reflection := angularClosedJet_reflection
  original_angular_bound := angularGradeCore_norm_le
  average_formula := equivariantAverageJet_value
  tangential_cartesian := tangentialJet_eq
  tangential_projection := tangentialJet_idempotent
  original_tangential_bound := tangentialGradeCore_norm_le
  average_polar := equivariantAverageJet_polar_formula
  tangential_polar := tangentialJet_polar_formula
  entire_disk_polar := closedPoint_has_polar_angle
  angular_zero_jets := angularClosedJet_preserves_zero_derivatives
  tangential_zero_jets := tangentialJet_preserves_zero_derivatives
  coordinate_shift := angularClosedJet_z
  conjugate_coordinate_shift := angularClosedJet_zbar
  laplacian_origin := angularClosedJet_laplacian_origin
  high_modes_projection := excludedAngularJet_idempotent lowAngularModes
  high_modes_bound := by
    intro dimension grade parameters field
    simpa only [lowAngularModes_card, Nat.cast_ofNat] using
      excludedAngularGradeCore_norm_le parameters lowAngularModes field

end Grad.Constraints
