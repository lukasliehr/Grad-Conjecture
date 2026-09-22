import AXL8SeedPoloidal

noncomputable section

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.PhysicalCoordinates Grad.ChartAxisSplit

variable {parameters : PhaseParameters}

theorem toPhysicalValue_tamePlanar (value : ComplexEuclidean 2) :
    toPhysicalValue (tamePlanarInclusion value) = Gauges.planarInclusionMap value := by
  rw [← toPhysicalValue_planar, toPhysicalValue_involutive]

theorem toPhysicalValue_tameTangent (value : ComplexEuclidean 1) :
    toPhysicalValue (tameTangentInclusion value) = Gauges.toroidalInclusionMap value := by
  rw [← toPhysicalValue_toroidal, toPhysicalValue_involutive]

theorem toPhysicalCore_tamePlanar (field : ACore parameters 2) :
    toPhysicalCore parameters (valueMapCore parameters tamePlanarInclusion field) =
      Gauges.planarInclusionCore parameters field := by
  apply acore_ext
  intro cell point
  rw [toPhysicalCore_value, valueMapCore_value, toPhysicalValue_tamePlanar]
  exact (valueMapJet_value Gauges.planarInclusionMap (field.val cell) point).symm

theorem toPhysicalCore_tameTangent (field : ACore parameters 1) :
    toPhysicalCore parameters (valueMapCore parameters tameTangentInclusion field) =
      Gauges.toroidalInclusionCore parameters field := by
  apply acore_ext
  intro cell point
  rw [toPhysicalCore_value, valueMapCore_value, toPhysicalValue_tameTangent]
  exact (valueMapJet_value Gauges.toroidalInclusionMap (field.val cell) point).symm

theorem storedAffineField_formula (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    toPhysicalCore parameters (chartAffineField parameters seed inside coefficient tangent 0) =
      Gauges.planarInclusionCore parameters (tameScalarMultiplier 2 coefficient
        (tameSeedPlanarField parameters seed inside)) +
      Gauges.toroidalInclusionCore parameters
        (tameScalarMultiplier 1 (tangentComponent tangent 0) (tameCoordinateScalarField parameters 0) +
          tameScalarMultiplier 1 (tangentComponent tangent 1) (tameCoordinateScalarField parameters 1)) := by
  rw [chartAffineField, add_zero, tameSeedField, tameScalarMultiplier_valueMap, map_add,
    toPhysicalCore_tamePlanar, toPhysicalCore_tameTangent]

theorem storedCapAffineField_formula (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    toPhysicalCore parameters (capAffineField parameters radius positive seed inside coefficient tangent) =
      Gauges.planarInclusionCore parameters (tameScalarMultiplier 2 coefficient
        (Gauges.seedMatrixCore parameters seed inside (capPlanarCoordinate parameters radius positive))) +
      Gauges.toroidalInclusionCore parameters (capScalarAffine parameters radius positive tangent) := by
  rw [capAffineField, capSeedField, tameScalarMultiplier_valueMap, map_add,
    toPhysicalCore_tamePlanar, toPhysicalCore_tameTangent]
  rfl

/-- AL15 vector remainder in the unchanged storage carrier. Its physical
interpretation is precisely the cap-supported variation minus its affine part. -/
def storedCapChartRemainder (parameters : PhaseParameters) (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) : ACore parameters 3 :=
  toPhysicalCore parameters (capChartRemainder parameters radius positive seed inside coefficient tangent)

theorem storedCapChartRemainder_zeroJets (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    ∀ cell, ZeroCartesianFirstJets
      ((storedCapChartRemainder parameters radius positive seed inside coefficient tangent).val cell) :=
  toPhysicalCore_zeroJets parameters _ (capChartRemainder_zeroJets radius positive seed inside coefficient tangent)

theorem storedCapChartRemainder_planar (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    Gauges.planarPartCore parameters
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent) =
        tameScalarMultiplier 2 coefficient (Gauges.seedMatrixCore parameters seed inside
          (capPlanarCoordinate parameters radius positive)) -
        tameScalarMultiplier 2 coefficient (tameSeedPlanarField parameters seed inside) := by
  rw [storedCapChartRemainder, capChartRemainder, map_sub,
    storedCapAffineField_formula, storedAffineField_formula, map_sub, map_add, map_add,
    Gauges.planarPartCore_planarInclusionCore, Gauges.planarPartCore_planarInclusionCore,
    Gauges.planarPartCore_toroidalInclusionCore, Gauges.planarPartCore_toroidalInclusionCore,
    add_zero, add_zero]

theorem storedCapChartRemainder_poloidal (radius : ℝ) (positive : 0 < radius)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    Gauges.poloidalCorrection parameters seed inside
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent) = 0 := by
  rw [Gauges.poloidalCorrection_apply, storedCapChartRemainder_planar, map_sub, map_sub]
  change Gauges.planarInclusionCore parameters (Gauges.seedMatrixCore parameters seed inside
    (tangentialCore parameters (seedPoloidalCap parameters radius positive seed inside coefficient) -
      tangentialCore parameters (seedPoloidalLinear parameters seed inside coefficient))) = 0
  rw [seedPoloidalCap_mean_zero, seedPoloidalLinear_mean_zero, sub_self, map_zero, map_zero]

end Grad.ChartAxisLift
