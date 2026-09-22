import GC18PolarMean

noncomputable section

set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.NonlinearDivision

theorem closedMeanIntegrand_continuous {Target : Type} [TopologicalSpace Target]
    (field : ClosedDisk → Target) (continuous : Continuous field) (point : ClosedDisk) :
    Continuous (fun time : ℝ => field (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)) := by
  have orbit := closedRotation_continuous field continuous point
  exact orbit.comp ((continuous_const : Continuous (fun _ : ℝ => 2 * Real.pi)).mul continuous_id)

theorem closedAngularMean_clm {Source Target : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source] [CompleteSpace Source]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    (mapping : Source →L[ℝ] Target) (field : ClosedDisk → Source) (continuous : Continuous field) (point : ClosedDisk) :
    mapping (closedAngularMean field point) = closedAngularMean (fun other => mapping (field other)) point := by
  unfold closedAngularMean
  exact (mapping.integral_comp_comm
    (closedMeanIntegrand_continuous field continuous point).continuousOn.integrableOn_Icc).symm

theorem closedCharacterProjection_origin {dimension : ℕ} (mode : ℤ)
    (field : ClosedDisk → ComplexEuclidean dimension) :
    closedCharacterProjection mode field closedOrigin = if mode = 0 then field closedOrigin else 0 := by
  rw [closedCharacterProjection_integral]
  simp_rw [radialRotatedPoint_origin]
  exact angularCharacter_normalized_integral mode _

theorem closedTangentialValue_origin (field : ClosedDisk → ComplexEuclidean 2) :
    closedTangentialValue field closedOrigin = 0 := by
  have reflected : orthogonalClosedPoint cartesianReflectionEquiv closedOrigin = closedOrigin := by
    apply Subtype.ext
    exact cartesianReflectionEquiv.map_zero
  rw [closedTangentialValue, reflected, closedEquivariantValue,
    closedCharacterProjection_origin, closedCharacterProjection_origin]
  norm_num

theorem closedAngularMean_origin {Target : Type} [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    (field : ClosedDisk → Target) : closedAngularMean field closedOrigin = field closedOrigin := by
  unfold closedAngularMean
  simp_rw [radialRotatedPoint_origin]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem cartesianComplementValue_origin (field : ClosedDisk → ComplexEuclidean 3) :
    cartesianComplementValue field closedOrigin = (field closedOrigin 2) • storedScalar := by
  rw [cartesianComplementValue, closedTangentialValue_origin, closedCharacterProjection_origin]
  simp [storedScalar, toroidalPartMap, toroidalInclusionMap]
  apply PiLp.ext
  intro row
  fin_cases row <;> simp

theorem fixedComplementValue_origin (field : ClosedDisk → ComplexEuclidean 3) :
    fixedComplementValue field closedOrigin = (field closedOrigin 2) • storedScalar := by
  unfold fixedComplementValue complementProfile
  rw [closedAngularMean_origin]
  have tangentZero : storedTangent closedOrigin = 0 := by
    apply PiLp.ext
    intro row
    fin_cases row <;> simp [storedTangent, closedOrigin]
  rw [tangentZero, smul_zero, zero_add]

theorem scalarMean_third (field : ClosedDisk → ComplexEuclidean 3) (continuous : Continuous field) (point : ClosedDisk) :
    (closedCharacterProjection 0 (fun other => toroidalPartMap (field other)) point) 0 =
      closedAngularMean (fun other => field other 2) point := by
  rw [closedCharacterProjection_zero]
  have identity := closedAngularMean_clm
    ((PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0 : ComplexEuclidean 1 →L[ℂ] ℂ).restrictScalars ℝ)
    (fun other => toroidalPartMap (field other)) (toroidalPartMap.continuous.comp continuous) point
  exact identity

theorem cartesianComplementValue_coordinates (field : ClosedDisk → ComplexEuclidean 3) (point : ClosedDisk) :
    cartesianComplementValue field point = WithLp.toLp 2 ![
      (closedTangentialValue (fun other => planarPartMap (field other)) point) 0,
      (closedTangentialValue (fun other => planarPartMap (field other)) point) 1,
      (closedCharacterProjection 0 (fun other => toroidalPartMap (field other)) point) 0] := by
  apply PiLp.ext
  intro row
  fin_cases row <;> simp [cartesianComplementValue, planarInclusionMap, toroidalInclusionMap]

theorem fixedComplementValue_coordinates (field : ClosedDisk → ComplexEuclidean 3) (point : ClosedDisk) :
    fixedComplementValue field point = WithLp.toLp 2 ![
      ((radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point) * (-(point.val 1 : ℂ)),
      ((radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point) * (point.val 0 : ℂ),
      closedAngularMean (fun other => field other 2) point] := by
  apply PiLp.ext
  intro row
  fin_cases row <;> simp [fixedComplementValue, complementProfile, storedTangent, storedScalar]

/-- The literal nonsingular Cartesian C0 and its polar evaluation formula
agree on every continuous physical field, including the axis. No divided
unknown is used to define the Cartesian operator. -/
theorem cartesianComplementValue_eq_polar (field : ClosedDisk → ComplexEuclidean 3)
    (continuous : Continuous field) (point : ClosedDisk) :
    cartesianComplementValue field point = fixedComplementValue field point := by
  by_cases axis : point.val = 0
  · have atOrigin : point = closedOrigin := Subtype.ext axis
    rw [atOrigin, cartesianComplementValue_origin, fixedComplementValue_origin]
  · obtain ⟨angle, polar⟩ := closedPoint_has_polar_angle point
    let radius := ‖point.val‖
    have bounded : |radius| ≤ 1 := by dsimp [radius]; rw [abs_norm]; exact point.property
    have tangent := closedTangentialValue_polar_formula (fun other => planarPartMap (field other))
      (planarPartMap.continuous.comp continuous) radius bounded angle
    have moment := closedMean_tangentDot_polar field radius bounded angle
    rw [show polarClosedPoint radius bounded angle = point from polar] at tangent moment
    have coordinates := congrArg Subtype.val polar
    rw [polarClosedPoint_coordinates] at coordinates
    have firstCoordinate := congrArg (fun value : SpatialPlane => value 0) coordinates
    have secondCoordinate := congrArg (fun value : SpatialPlane => value 1) coordinates
    change radius * Real.cos angle = point.val 0 at firstCoordinate
    change radius * Real.sin angle = point.val 1 at secondCoordinate
    have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr axis)
    rw [cartesianComplementValue_coordinates, fixedComplementValue_coordinates]
    apply PiLp.ext
    intro row
    fin_cases row
    · change (closedTangentialValue (fun other => planarPartMap (field other)) point) 0 =
        ((radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point) * (-(point.val 1 : ℂ))
      rw [tangent, moment, ← secondCoordinate]
      rw [radiusScalar, Complex.ofReal_pow]
      change closedPolarTangentialMean (fun other => planarPartMap (field other)) radius bounded angle * (-(Real.sin angle : ℂ)) =
        (((radius : ℂ) ^ 2)⁻¹ * ((radius : ℂ) * closedPolarTangentialMean (fun other => planarPartMap (field other)) radius bounded angle)) * (-((radius * Real.sin angle : ℝ) : ℂ))
      push_cast
      field_simp
    · change (closedTangentialValue (fun other => planarPartMap (field other)) point) 1 =
        ((radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point) * (point.val 0 : ℂ)
      rw [tangent, moment, ← firstCoordinate]
      rw [radiusScalar, Complex.ofReal_pow]
      change closedPolarTangentialMean (fun other => planarPartMap (field other)) radius bounded angle * (Real.cos angle : ℂ) =
        (((radius : ℂ) ^ 2)⁻¹ * ((radius : ℂ) * closedPolarTangentialMean (fun other => planarPartMap (field other)) radius bounded angle)) * ((radius * Real.cos angle : ℝ) : ℂ)
      push_cast
      field_simp
    · change (closedCharacterProjection 0 (fun other => toroidalPartMap (field other)) point) 0 =
        closedAngularMean (fun other => field other 2) point
      exact scalarMean_third field continuous point

end Grad.GaugeCoefficients.Physical.RadialLedger
