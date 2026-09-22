import AngularProjectionAlgebra
import CompactIntegralDerivatives

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.PhysicalFamily Grad.GaugeCoefficients.Radial

theorem angularProjectionIntegrand_smooth {dimension : ℕ} (mode : ℤ)
    {field : SpatialPlane → ComplexEuclidean dimension} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      angularCharacter mode argument.2 • field (planeRotationAction argument.2 argument.1)) := by
  have rotationSmooth : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      planeRotationAction argument.2 argument.1) := by
    rw [contDiff_piLp]
    intro coordinate
    fin_cases coordinate <;>
      simp [planeRotationAction, Grad.GeometryClosure.planarRotation, Matrix.vecHead, Matrix.vecTail] <;>
      fun_prop
  exact ((angularCharacter_smooth mode).comp contDiff_snd).smul (smooth.comp rotationSmooth)

theorem angularProjectionValue_derivative {dimension order : ℕ} (mode : ℤ)
    {field : SpatialPlane → ComplexEuclidean dimension} (smooth : ContDiff ℝ ∞ field)
    (word : CartesianWord order) (point : SpatialPlane) :
    cartesianDerivative order word (angularProjectionValue mode field) point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        cartesianDerivative order word
          (fun source => angularCharacter mode angle • field (planeRotationAction angle source)) point := by
  let integrand : SpatialPlane × ℝ → ComplexEuclidean dimension := fun argument =>
    angularCharacter mode argument.2 • field (planeRotationAction argument.2 argument.1)
  have integrandSmooth : ContDiff ℝ ∞ integrand := angularProjectionIntegrand_smooth mode smooth
  have integralSmooth : ContDiff ℝ ∞
      (fun source => ∫ angle in Icc (0 : ℝ) (2 * Real.pi), integrand (source, angle)) :=
    contDiffOn_univ.mp (contDiffOn_compactIntegral isOpen_univ integrandSmooth.contDiffOn 0 (2 * Real.pi))
  have derivativeSmul := iteratedFDeriv_const_smul_apply (x := point) (a := ((2 * Real.pi)⁻¹ : ℝ))
    (integralSmooth.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top)))
  have functionEquality : angularProjectionValue mode field =
      fun source => (2 * Real.pi)⁻¹ •
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi), integrand (source, angle) := by
    funext source
    exact angularProjectionValue_eq_compactIntegral mode field source
  rw [functionEquality]
  exact (congrArg (fun derivative => derivative (fun position => spatialBasis (word position)))
      derivativeSmul).trans
    (congrArg (fun value => ((2 * Real.pi)⁻¹ : ℝ) • value)
      (cartesianDerivative_compactIntegral order word integrandSmooth 0 (2 * Real.pi) point))

theorem globalRotatedCharacter_restricts {dimension : ℕ} (mode : ℤ) (angle : ℝ)
    (field : ClosedJet dimension) :
    globalClosedJet
        (fun source => angularCharacter mode angle •
          smoothClosedExtension field (planeRotationAction angle source))
        ((angularProjectionIntegrand_smooth mode (smoothClosedExtension_smooth field)).comp
          (contDiff_id.prodMk contDiff_const)) =
      angularCharacter mode angle • orthogonalJet (planeRotationEquiv angle) field := by
  apply globalClosedJet_eq_of_restriction
  intro point
  change angularCharacter mode angle • smoothClosedExtension field (planeRotationAction angle point.val) =
    angularCharacter mode angle • field.value (orthogonalClosedPoint (planeRotationEquiv angle) point)
  rw [physicalRotation_eq_orthogonal]
  exact congrArg (fun value => angularCharacter mode angle • value)
    (smoothClosedExtension_value field (orthogonalClosedPoint (planeRotationEquiv angle) point))

theorem globalRotatedCharacter_derivative {dimension order : ℕ} (mode : ℤ) (angle : ℝ)
    (field : ClosedJet dimension) (word : CartesianWord order) (point : ClosedDisk) :
    cartesianDerivative order word
        (fun source => angularCharacter mode angle •
          smoothClosedExtension field (planeRotationAction angle source)) point.val =
      angularCharacter mode angle •
        orthogonalDerivative (planeRotationEquiv angle) field order word point := by
  have equality := globalRotatedCharacter_restricts mode angle field
  have derivativeEquality := congrArg (fun jet => closedDerivative jet order word point) equality
  rw [globalClosedJet_derivative] at derivativeEquality
  change _ = closedDerivative (closedJetSmul (angularCharacter mode angle)
    (orthogonalJet (planeRotationEquiv angle) field)) order word point at derivativeEquality
  rw [closedJetSmul_derivative] at derivativeEquality
  change _ = angularCharacter mode angle •
    closedDerivative (orthogonalJet (planeRotationEquiv angle) field) order word point at derivativeEquality
  rw [orthogonalJet_derivative] at derivativeEquality
  exact derivativeEquality

/-- Every literal Cartesian derivative, including the boundary, commutes with
the specified angular projector. No extension norm enters this identity. -/
theorem angularClosedJet_derivative {dimension order : ℕ} (mode : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (angularClosedJet mode field) order word point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        angularCharacter mode angle •
          orthogonalDerivative (planeRotationEquiv angle) field order word point := by
  rw [angularClosedJet, globalClosedJet_derivative,
    angularProjectionValue_derivative mode (smoothClosedExtension_smooth field)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  exact globalRotatedCharacter_derivative mode angle field word point

end Grad.Constraints
