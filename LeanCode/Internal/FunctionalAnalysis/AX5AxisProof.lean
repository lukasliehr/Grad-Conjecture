import AX4AxisInterface

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

/-- The actual COR08 axis-grade theorem. -/
theorem actualAxisGrade : AxisGradeGoal := by
  intro parameters valueDimension grade
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun field => axis_norm_sq parameters grade field
  · exact fun field => axis_l2_identification parameters grade field
  · exact fun family =>
      ⟨fun cell => axisEta_coefficient parameters valueDimension grade family cell,
        axisEta_norm_sq parameters valueDimension grade family⟩
  · exact fun first second equal =>
      axisEta_injective parameters valueDimension grade first second equal
  · exact fun field =>
      ⟨axisInvolution_involutive parameters valueDimension grade field,
        axisInvolution_norm parameters valueDimension grade field⟩
  · exact fun first second =>
      axisInvolution_add parameters valueDimension grade first second
  · exact fun scalar field =>
      axisInvolution_smul parameters valueDimension grade scalar field
  · exact fun family =>
      ⟨axisCoreInvolution_involutive parameters valueDimension family,
        axisEta_involution parameters valueDimension grade family⟩
  · exact fun field epsilon positive =>
      axis_finite_support_dense parameters valueDimension grade field epsilon positive
  · exact fun field =>
      ⟨fun cell => axisInclusion_coefficient parameters valueDimension grade field cell,
        axisInclusion_contractive parameters valueDimension grade field⟩
  · exact fun first second equal =>
      axisInclusion_injective parameters valueDimension grade first second equal
  · exact fun field => axisInvolution_inclusion parameters valueDimension grade field

end Grad.AxisCore
