import CircleIsometryClassificationInterface

noncomputable section

namespace Grad.MainAssembly.CircleIsometryClassification

/-- Exact closed `NG_R07` public boundary. -/
theorem circleIsometryClassification : CircleIsometryClassificationGoal := by
  intro radius orthogonal translation radiusPositive axisEquality
  exact circlePreserving_isometry_classification radius orthogonal translation
    radiusPositive axisEquality

end Grad.MainAssembly.CircleIsometryClassification
