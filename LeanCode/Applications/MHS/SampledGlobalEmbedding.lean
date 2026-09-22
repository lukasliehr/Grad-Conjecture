import SampledFullGeometryConsumer
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

noncomputable section

open Set

namespace Grad.PhysicalFamily.SampledGlobalEmbedding

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledAllTimeBounds
open Grad.PhysicalFamily.SampledFullGeometry
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.SampledAxisBasics
open Grad.MainAssembly.PhysicalNormalHessian

local instance : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

private theorem sqrt_one_add_div_sq
    (radial tangential : ℝ) (radialPositive : 0 < radial) :
    Real.sqrt (1 + (tangential / radial) ^ 2) =
      Real.sqrt (radial ^ 2 + tangential ^ 2) / radial := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
    (div_nonneg (Real.sqrt_nonneg _) radialPositive.le)).mp
  rw [Real.sq_sqrt (by positivity)]
  simp only [div_pow]
  rw [Real.sq_sqrt (by positivity)]
  field_simp [radialPositive.ne']

theorem cylindricalAngle_cos
    (radial tangential : ℝ) (radialPositive : 0 < radial) :
    Real.sqrt (radial ^ 2 + tangential ^ 2) *
        Real.cos (Real.arctan (tangential / radial)) = radial := by
  rw [Real.cos_arctan,
    sqrt_one_add_div_sq radial tangential radialPositive]
  have radiusPositive : 0 < Real.sqrt (radial ^ 2 + tangential ^ 2) := by
    exact Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos radialPositive) (sq_nonneg _))
  field_simp [radialPositive.ne', radiusPositive.ne']

theorem cylindricalAngle_sin
    (radial tangential : ℝ) (radialPositive : 0 < radial) :
    Real.sqrt (radial ^ 2 + tangential ^ 2) *
        Real.sin (Real.arctan (tangential / radial)) = tangential := by
  rw [Real.sin_arctan,
    sqrt_one_add_div_sq radial tangential radialPositive]
  have radiusPositive : 0 < Real.sqrt (radial ^ 2 + tangential ^ 2) := by
    exact Real.sqrt_pos.2
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos radialPositive) (sq_nonneg _))
  field_simp [radialPositive.ne', radiusPositive.ne']

theorem rotation_cylindrical_factorization
    (time radial tangential vertical : ℝ) (radialPositive : 0 < radial) :
    rotation time (vector radial tangential vertical) =
      rotation (time + Real.arctan (tangential / radial))
        (vector (Real.sqrt (radial ^ 2 + tangential ^ 2)) 0 vertical) := by
  have cosineIdentity := cylindricalAngle_cos radial tangential radialPositive
  have sineIdentity := cylindricalAngle_sin radial tangential radialPositive
  ext coordinate
  fin_cases coordinate
  · simp [rotation, vector, Real.cos_add, Real.sin_add]
    linear_combination -Real.cos time * cosineIdentity +
      Real.sin time * sineIdentity
  · simp [rotation, vector, Real.cos_add, Real.sin_add]
    linear_combination -Real.sin time * cosineIdentity -
      Real.cos time * sineIdentity
  · simp [rotation, vector]

theorem rotation_radial_data_injective
    (firstAngle secondAngle firstRadius secondRadius firstVertical
      secondVertical : ℝ)
    (firstRadiusPositive : 0 < firstRadius)
    (secondRadiusPositive : 0 < secondRadius)
    (equality :
      rotation firstAngle (vector firstRadius 0 firstVertical) =
        rotation secondAngle (vector secondRadius 0 secondVertical)) :
    firstRadius = secondRadius ∧
      (firstAngle : CellCircle) = (secondAngle : CellCircle) ∧
      firstVertical = secondVertical := by
  have coordinateZero := congrArg (fun point : Vec => point 0) equality
  have coordinateOne := congrArg (fun point : Vec => point 1) equality
  have coordinateTwo := congrArg (fun point : Vec => point 2) equality
  simp [rotation, vector] at coordinateZero coordinateOne coordinateTwo
  have firstSquares :
      (Real.cos firstAngle * firstRadius) ^ 2 +
          (Real.sin firstAngle * firstRadius) ^ 2 = firstRadius ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq firstAngle]
  have secondSquares :
      (Real.cos secondAngle * secondRadius) ^ 2 +
          (Real.sin secondAngle * secondRadius) ^ 2 = secondRadius ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq secondAngle]
  have radiusSquares : firstRadius ^ 2 = secondRadius ^ 2 := by
    rw [← firstSquares, coordinateZero, coordinateOne, secondSquares]
  have radiusEquality : firstRadius = secondRadius :=
    (sq_eq_sq₀ firstRadiusPositive.le secondRadiusPositive.le).mp
      radiusSquares
  rw [radiusEquality] at coordinateZero coordinateOne
  have cosineEquality : Real.cos firstAngle = Real.cos secondAngle := by
    apply mul_right_cancel₀ secondRadiusPositive.ne'
    exact coordinateZero
  have sineEquality : Real.sin firstAngle = Real.sin secondAngle := by
    apply mul_right_cancel₀ secondRadiusPositive.ne'
    exact coordinateOne
  have angleEquality : (firstAngle : CellCircle) = secondAngle := by
    have realAngleEquality :=
      Real.Angle.cos_sin_inj cosineEquality sineEquality
    change (firstAngle : CellCircle) = (secondAngle : CellCircle) at realAngleEquality
    exact realAngleEquality
  exact ⟨radiusEquality, angleEquality, coordinateTwo⟩

def sampledCylindricalRadius
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Plane) (cellTime : ℝ) : ℝ :=
  Real.sqrt ((((period : ℝ) * cellLength) +
      (family.v (sampledEpsilon period) parameter point cellTime) 0) ^ 2 +
    ((family.v (sampledEpsilon period) parameter point cellTime) 1) ^ 2)

def sampledCylindricalAngleCorrection
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Plane) (cellTime : ℝ) : ℝ :=
  Real.arctan
    ((family.v (sampledEpsilon period) parameter point cellTime) 1 /
      (((period : ℝ) * cellLength) +
        (family.v (sampledEpsilon period) parameter point cellTime) 0))

def sampledCellCoverMap
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (argument : Vec) : Vec :=
  coordinateDirection
    (WithLp.toLp 2
      ![sampledCylindricalRadius cellLength family period parameter
          (planarPart argument) (argument 2) - (period : ℝ) * cellLength,
        (family.v (sampledEpsilon period) parameter (planarPart argument)
          (argument 2)) 2])
    (argument 2 + (period : ℝ) *
      sampledCylindricalAngleCorrection cellLength family period parameter
        (planarPart argument) (argument 2))

def sampledNormalizedCellCoverMap
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (argument : Vec) : Vec :=
  let cylindrical := sampledCellCoverMap cellLength family period parameter
    argument
  let phase := cylindrical 2
  coordinateDirection
    (WithLp.toLp 2
      (Matrix.mulVec
        (Grad.GeometryClosure.seedInverse family.rho
          (Grad.GeometryClosure.seedAngle family.alpha family.delta parameter
            phase))
        (fun coordinate => (planarPart cylindrical) coordinate)))
    phase

theorem sampledCellCover_injective_of_normalized_injective
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ)
    (normalizedInjective : Set.InjOn
      (sampledNormalizedCellCoverMap cellLength family period parameter)
      cylinder) :
    Set.InjOn (sampledCellCoverMap cellLength family period parameter)
      cylinder := by
  intro first firstIn second secondIn equality
  apply normalizedInjective firstIn secondIn
  unfold sampledNormalizedCellCoverMap
  rw [equality]

theorem sampled_major_radial_positive
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (cellTime : ℝ)
    (errorSmall : family.bound * |sampledEpsilon period| ≤ 1)
    (radiusLarge : 4 < (period : ℝ) * cellLength) :
    0 < (period : ℝ) * cellLength +
      (family.v (sampledEpsilon period) parameter.val point cellTime) 0 := by
  have valueBound := v_norm_le_four cellLength family
    (sampledEpsilon period) epsilonIn parameter point pointIn cellTime
    errorSmall
  have coordinateBound := coordinate_abs_le_norm
    (family.v (sampledEpsilon period) parameter.val point cellTime) 0
  have coordinateLower :
      -4 ≤ (family.v (sampledEpsilon period) parameter.val point cellTime) 0 := by
    have absoluteBound :
        |(family.v (sampledEpsilon period) parameter.val point cellTime) 0| ≤
          4 := coordinateBound.trans valueBound
    exact (abs_le.mp absoluteBound).1
  linarith

theorem sampledCylindricalRadius_positive
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Plane) (cellTime : ℝ)
    (radialPositive : 0 < (period : ℝ) * cellLength +
      (family.v (sampledEpsilon period) parameter point cellTime) 0) :
    0 < sampledCylindricalRadius cellLength family period parameter point
      cellTime := by
  unfold sampledCylindricalRadius
  apply Real.sqrt_pos.2
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos radialPositive) (sq_nonneg _)

/-- The cylindrical tangential component is genuinely perturbative.  The
harmonic seed has no tangent-coordinate component, so only the stored tilt
and remainder contribute.  This is the order-zero part of the uniform G08
angular-correction estimate. -/
theorem sampled_v_tangential_abs_le_two_error
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (cellTime : ℝ) :
    |(family.v epsilon parameter.val point cellTime) 1| ≤
      2 * (family.bound * |epsilon|) := by
  rw [family.normalizedChart epsilon epsilonIn parameter.val
    parameter.property point pointIn cellTime]
  have tiltBound := tilt_value_norm_le_physicalBound_allTime cellLength family
    epsilon epsilonIn parameter cellTime
  have remainderBound := remainder_value_norm_le_physicalBound_allTime
    cellLength family epsilon epsilonIn parameter point pointIn cellTime
  have errorNonnegative : 0 ≤ family.bound * |epsilon| :=
    mul_nonneg (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _)
  simp [planeEmbedding, tangentDirection, basisVector, vector, smul_eq_mul]
  calc
    |planeDot (family.tilt epsilon parameter.val cellTime) point +
        (family.remainder epsilon parameter.val point cellTime) 1| ≤
      |planeDot (family.tilt epsilon parameter.val cellTime) point| +
        |(family.remainder epsilon parameter.val point cellTime) 1| :=
      abs_add_le _ _
    _ ≤ ‖family.tilt epsilon parameter.val cellTime‖ * ‖point‖ +
        ‖family.remainder epsilon parameter.val point cellTime‖ :=
      add_le_add (abs_planeDot_le_norm_mul_norm _ _)
        (coordinate_abs_le_norm _ 1)
    _ ≤ (family.bound * |epsilon|) * 1 +
        family.bound * |epsilon| :=
      add_le_add
        (mul_le_mul tiltBound pointIn (norm_nonneg _) errorNonnegative)
        remainderBound
    _ = 2 * (family.bound * |epsilon|) := by ring

theorem sampledCellCoverMap_coordinateDirection
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Plane) (cellTime : ℝ) :
    sampledCellCoverMap cellLength family period parameter
        (coordinateDirection point cellTime) =
      coordinateDirection
        (WithLp.toLp 2
          ![sampledCylindricalRadius cellLength family period parameter point
              cellTime - (period : ℝ) * cellLength,
            (family.v (sampledEpsilon period) parameter point cellTime) 2])
        (cellTime + (period : ℝ) *
          sampledCylindricalAngleCorrection cellLength family period parameter
            point cellTime) := by
  have planarIdentity : planarPart (coordinateDirection point cellTime) =
      point := by
    ext coordinate
    fin_cases coordinate <;>
      simp [planarPart, coordinateDirection, vector]
  have timeIdentity : (coordinateDirection point cellTime) 2 = cellTime := by
    simp [coordinateDirection, vector]
  unfold sampledCellCoverMap
  rw [planarIdentity, timeIdentity]

private theorem sampled_v_add_int_period
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (cellTime : ℝ) (count : ℤ) :
    family.v (sampledEpsilon period) parameter.val point
        (cellTime + (count : ℝ) * (2 * Real.pi)) =
      family.v (sampledEpsilon period) parameter.val point cellTime := by
  have parameterIn := parameter_mem_open cellLength family parameter
  have pointInCollar : point ∈ Metric.ball (0 : Plane) family.collarRadius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have vPeriodic : Function.Periodic
      (family.v (sampledEpsilon period) parameter.val point)
      (2 * Real.pi) :=
    family.vPeriodic (sampledEpsilon period) epsilonIn parameter.val
      parameterIn point pointInCollar
  exact (vPeriodic.int_mul count) cellTime

theorem sampledCylindricalRadius_add_int_period
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (cellTime : ℝ) (count : ℤ) :
    sampledCylindricalRadius cellLength family period parameter.val point
        (cellTime + (count : ℝ) * (2 * Real.pi)) =
      sampledCylindricalRadius cellLength family period parameter.val point
        cellTime := by
  unfold sampledCylindricalRadius
  rw [sampled_v_add_int_period cellLength family period epsilonIn parameter
    point pointIn cellTime count]

theorem sampledCylindricalAngleCorrection_add_int_period
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (cellTime : ℝ) (count : ℤ) :
    sampledCylindricalAngleCorrection cellLength family period parameter.val
        point (cellTime + (count : ℝ) * (2 * Real.pi)) =
      sampledCylindricalAngleCorrection cellLength family period parameter.val
        point cellTime := by
  unfold sampledCylindricalAngleCorrection
  rw [sampled_v_add_int_period cellLength family period epsilonIn parameter
    point pointIn cellTime count]

theorem sampledPositionLift_cylindrical_factorization
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Plane) (time : ℝ)
    (radialPositive : 0 < (period : ℝ) * cellLength +
      (family.v (sampledEpsilon period) parameter point
        ((period : ℝ) * time)) 0) :
    sampledPositionLift cellLength family period parameter point time =
      rotation
        (time + sampledCylindricalAngleCorrection cellLength family period
          parameter point ((period : ℝ) * time))
        (vector
          (sampledCylindricalRadius cellLength family period parameter point
            ((period : ℝ) * time))
          0
          ((family.v (sampledEpsilon period) parameter point
            ((period : ℝ) * time)) 2)) := by
  let value := family.v (sampledEpsilon period) parameter point
    ((period : ℝ) * time)
  have inputIdentity :
      ((period : ℝ) * cellLength) • basisVector 0 + value =
        vector (((period : ℝ) * cellLength) + value 0) (value 1) (value 2) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [basisVector, vector, smul_eq_mul]
  unfold sampledPositionLift
  rw [show ((period : ℝ) * cellLength) = period * cellLength by rfl]
  rw [inputIdentity]
  simpa [value, sampledCylindricalRadius,
    sampledCylindricalAngleCorrection] using
    rotation_cylindrical_factorization time
      (((period : ℝ) * cellLength) + value 0) (value 1) (value 2)
      radialPositive

/-- The integer-lift part of global injectivity.  Once the cylindrical
cell-cover map is injective on the closed universal cylinder, a collision of
two physical real lifts identifies both disk points and their physical angles
in the target circle. -/
theorem sampledPositionLift_collision_of_cellCover_injective
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (errorSmall : family.bound * |sampledEpsilon period| ≤ 1)
    (radiusLarge : 4 < (period : ℝ) * cellLength)
    (cellCoverInjective : Set.InjOn
      (sampledCellCoverMap cellLength family period parameter.val) cylinder)
    (firstPoint secondPoint : Plane)
    (firstPointIn : ‖firstPoint‖ ≤ 1)
    (secondPointIn : ‖secondPoint‖ ≤ 1)
    (firstTime secondTime : ℝ)
    (positionEquality :
      sampledPositionLift cellLength family period parameter.val firstPoint
          firstTime =
        sampledPositionLift cellLength family period parameter.val secondPoint
          secondTime) :
    firstPoint = secondPoint ∧
      (firstTime : CellCircle) = (secondTime : CellCircle) := by
  let firstCellTime := (period : ℝ) * firstTime
  let secondCellTime := (period : ℝ) * secondTime
  let firstValue := family.v (sampledEpsilon period) parameter.val firstPoint
    firstCellTime
  let secondValue := family.v (sampledEpsilon period) parameter.val secondPoint
    secondCellTime
  let firstRadius := sampledCylindricalRadius cellLength family period
    parameter.val firstPoint firstCellTime
  let secondRadius := sampledCylindricalRadius cellLength family period
    parameter.val secondPoint secondCellTime
  let firstCorrection := sampledCylindricalAngleCorrection cellLength family
    period parameter.val firstPoint firstCellTime
  let secondCorrection := sampledCylindricalAngleCorrection cellLength family
    period parameter.val secondPoint secondCellTime
  have firstRadialPositive := sampled_major_radial_positive cellLength family
    period epsilonIn parameter firstPoint firstPointIn firstCellTime errorSmall
    radiusLarge
  have secondRadialPositive := sampled_major_radial_positive cellLength family
    period epsilonIn parameter secondPoint secondPointIn secondCellTime
    errorSmall radiusLarge
  have firstRadiusPositive : 0 < firstRadius := by
    exact sampledCylindricalRadius_positive cellLength family period
      parameter.val firstPoint firstCellTime firstRadialPositive
  have secondRadiusPositive : 0 < secondRadius := by
    exact sampledCylindricalRadius_positive cellLength family period
      parameter.val secondPoint secondCellTime secondRadialPositive
  have cylindricalEquality :
      rotation (firstTime + firstCorrection)
          (vector firstRadius 0 (firstValue 2)) =
        rotation (secondTime + secondCorrection)
          (vector secondRadius 0 (secondValue 2)) := by
    rw [← sampledPositionLift_cylindrical_factorization cellLength family
      period parameter.val firstPoint firstTime firstRadialPositive,
      ← sampledPositionLift_cylindrical_factorization cellLength family
      period parameter.val secondPoint secondTime secondRadialPositive]
    exact positionEquality
  obtain ⟨radiusEquality, angleEquality, verticalEquality⟩ :=
    rotation_radial_data_injective
      (firstTime + firstCorrection) (secondTime + secondCorrection)
      firstRadius secondRadius (firstValue 2) (secondValue 2)
      firstRadiusPositive secondRadiusPositive cylindricalEquality
  have realAngleEquality :
      ((firstTime + firstCorrection : ℝ) : Real.Angle) =
        ((secondTime + secondCorrection : ℝ) : Real.Angle) := by
    change (firstTime + firstCorrection : CellCircle) =
      (secondTime + secondCorrection : CellCircle) at angleEquality
    change (firstTime + firstCorrection : Real.Angle) =
      (secondTime + secondCorrection : Real.Angle)
    exact angleEquality
  obtain ⟨count, angleDifference⟩ :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp realAngleEquality
  let totalCount : ℤ := (period : ℤ) * count
  let shiftedSecondCellTime := secondCellTime +
    (totalCount : ℝ) * (2 * Real.pi)
  let firstArgument := coordinateDirection firstPoint firstCellTime
  let secondArgument := coordinateDirection secondPoint shiftedSecondCellTime
  have firstArgumentIn : firstArgument ∈ cylinder := by
    change ‖planarPart firstArgument‖ ≤ 1
    have planarIdentity : planarPart firstArgument = firstPoint := by
      ext coordinate
      fin_cases coordinate <;>
        simp [firstArgument, planarPart, coordinateDirection, vector]
    rw [planarIdentity]
    exact firstPointIn
  have secondArgumentIn : secondArgument ∈ cylinder := by
    change ‖planarPart secondArgument‖ ≤ 1
    have planarIdentity : planarPart secondArgument = secondPoint := by
      ext coordinate
      fin_cases coordinate <;>
        simp [secondArgument, planarPart, coordinateDirection, vector]
    rw [planarIdentity]
    exact secondPointIn
  have shiftedRadius :
      sampledCylindricalRadius cellLength family period parameter.val
          secondPoint shiftedSecondCellTime = secondRadius := by
    dsimp [shiftedSecondCellTime, secondRadius]
    exact sampledCylindricalRadius_add_int_period cellLength family period
      epsilonIn parameter secondPoint secondPointIn secondCellTime totalCount
  have shiftedCorrection :
      sampledCylindricalAngleCorrection cellLength family period parameter.val
          secondPoint shiftedSecondCellTime = secondCorrection := by
    dsimp [shiftedSecondCellTime, secondCorrection]
    exact sampledCylindricalAngleCorrection_add_int_period cellLength family
      period epsilonIn parameter secondPoint secondPointIn secondCellTime
      totalCount
  have shiftedValue :
      family.v (sampledEpsilon period) parameter.val secondPoint
          shiftedSecondCellTime = secondValue := by
    dsimp [shiftedSecondCellTime, secondValue]
    exact sampled_v_add_int_period cellLength family period epsilonIn parameter
      secondPoint secondPointIn secondCellTime totalCount
  have coverEquality :
      sampledCellCoverMap cellLength family period parameter.val firstArgument =
        sampledCellCoverMap cellLength family period parameter.val
          secondArgument := by
    rw [show firstArgument = coordinateDirection firstPoint firstCellTime by rfl,
      show secondArgument =
        coordinateDirection secondPoint shiftedSecondCellTime by rfl,
      sampledCellCoverMap_coordinateDirection,
      sampledCellCoverMap_coordinateDirection]
    rw [shiftedRadius, shiftedCorrection, shiftedValue]
    ext coordinate
    fin_cases coordinate
    · simp [firstRadius, secondRadius, secondValue,
        coordinateDirection, vector, radiusEquality]
    · simp [firstValue, secondRadius, secondValue,
        coordinateDirection, vector, verticalEquality]
    · simp [coordinateDirection, vector, shiftedSecondCellTime,
        firstCellTime, secondCellTime, totalCount]
      have scaledDifference := congrArg (fun value : ℝ => (period : ℝ) * value)
        angleDifference
      nlinarith
  have argumentEquality : firstArgument = secondArgument :=
    cellCoverInjective firstArgumentIn secondArgumentIn coverEquality
  have pointEquality : firstPoint = secondPoint := by
    ext coordinate
    fin_cases coordinate
    · have evaluated := congrArg (fun point : Vec => point 0) argumentEquality
      simpa [firstArgument, secondArgument, coordinateDirection, vector] using
        evaluated
    · have evaluated := congrArg (fun point : Vec => point 1) argumentEquality
      simpa [firstArgument, secondArgument, coordinateDirection, vector] using
        evaluated
  have cellTimeEquality : firstCellTime = shiftedSecondCellTime := by
    have timeEquality := congrArg (fun point : Vec => point 2) argumentEquality
    simpa [firstArgument, secondArgument, coordinateDirection, vector] using
      timeEquality
  have physicalTimeDifference :
      firstTime - secondTime = 2 * Real.pi * (count : ℝ) := by
    dsimp [firstCellTime, secondCellTime, shiftedSecondCellTime, totalCount] at cellTimeEquality
    push_cast at cellTimeEquality
    have periodRealPositive : (0 : ℝ) < period := Nat.cast_pos.mpr periodPositive
    have factored : (period : ℝ) *
        ((firstTime - secondTime) - 2 * Real.pi * (count : ℝ)) = 0 := by
      calc
        _ = (period : ℝ) * firstTime -
            ((period : ℝ) * secondTime +
              ((period : ℝ) * (count : ℝ)) * (2 * Real.pi)) := by ring
        _ = 0 := by rw [cellTimeEquality]; ring
    have innerZero := (mul_eq_zero.mp factored).resolve_left
      periodRealPositive.ne'
    linarith
  have physicalAngleEquality :
      (firstTime : CellCircle) = (secondTime : CellCircle) := by
    have realEquality :
        (firstTime : Real.Angle) = (secondTime : Real.Angle) :=
      Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
        ⟨count, physicalTimeDifference⟩
    change (firstTime : CellCircle) = (secondTime : CellCircle) at realEquality
    exact realEquality
  exact ⟨pointEquality, physicalAngleEquality⟩

theorem sampledRepresentative_position_injective_of_cellCover
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Set.Icc family.lower family.upper)
    (errorSmall : family.bound * |sampledEpsilon period| ≤ 1)
    (radiusLarge : 4 < (period : ℝ) * cellLength)
    (cellCoverInjective : Set.InjOn
      (sampledCellCoverMap cellLength family period parameter.val) cylinder) :
    Function.Injective
      (sampledRepresentativeFamily cellLength family period epsilonIn potential
        parameter).position := by
  intro first second equality
  let firstTime :=
    (AddCircle.equivIco (2 * Real.pi) 0 first.2).val
  let secondTime :=
    (AddCircle.equivIco (2 * Real.pi) 0 second.2).val
  have firstTimeCoe : (firstTime : CellCircle) = first.2 := by
    exact (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply first.2
  have secondTimeCoe : (secondTime : CellCircle) = second.2 := by
    exact (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply second.2
  have firstIdentity : first = (first.1, (firstTime : CellCircle)) := by
    apply Prod.ext
    · rfl
    · exact firstTimeCoe.symm
  have secondIdentity : second = (second.1, (secondTime : CellCircle)) := by
    apply Prod.ext
    · rfl
    · exact secondTimeCoe.symm
  have parameterIn := parameter_mem_open cellLength family parameter
  have liftEquality :
      sampledPositionLift cellLength family period parameter.val first.1.val
          firstTime =
        sampledPositionLift cellLength family period parameter.val second.1.val
          secondTime := by
    rw [firstIdentity, secondIdentity] at equality
    simpa [sampledRepresentativeFamily, sampledRepresentativeExtension,
      parameterIn] using equality
  obtain ⟨pointEquality, angleEquality⟩ :=
    sampledPositionLift_collision_of_cellCover_injective cellLength family
      period periodPositive epsilonIn parameter errorSmall radiusLarge
      cellCoverInjective first.1.val second.1.val first.1.property
      second.1.property firstTime secondTime liftEquality
  apply Prod.ext
  · exact Subtype.ext pointEquality
  · calc
      first.2 = (firstTime : CellCircle) := firstTimeCoe.symm
      _ = (secondTime : CellCircle) := angleEquality
      _ = second.2 := secondTimeCoe

/-- Quantitative global injectivity on a convex set from an ambient
derivative bound around the identity.  This is the boundary-inclusive segment
step used by the sampled cell-cover map. -/
theorem one_sub_mul_norm_le_norm_image_sub_of_fderiv_close
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (mapping : Space → Space) (domain : Set Space) (domainConvex : Convex ℝ domain)
    (error : ℝ) (mappingDifferentiable : ∀ point ∈ domain,
      DifferentiableAt ℝ mapping point)
    (derivativeClose : ∀ point ∈ domain,
      ‖fderiv ℝ mapping point - ContinuousLinearMap.id ℝ Space‖ ≤ error)
    (first : Space) (firstIn : first ∈ domain)
    (second : Space) (secondIn : second ∈ domain) :
    (1 - error) * ‖second - first‖ ≤ ‖mapping second - mapping first‖ := by
  have meanValue := Convex.norm_image_sub_le_of_norm_fderiv_le'
    mappingDifferentiable derivativeClose domainConvex firstIn secondIn
  have meanValue' :
      ‖mapping second - mapping first - (second - first)‖ ≤
        error * ‖second - first‖ := by
    simpa using meanValue
  have triangle : ‖second - first‖ ≤
      ‖mapping second - mapping first‖ +
        ‖mapping second - mapping first - (second - first)‖ := by
    calc
      ‖second - first‖ =
          ‖(mapping second - mapping first) -
            (mapping second - mapping first - (second - first))‖ := by
        congr 1
        abel
      _ ≤ ‖mapping second - mapping first‖ +
          ‖mapping second - mapping first - (second - first)‖ :=
        norm_sub_le _ _
  have errorNonnegative : 0 ≤ error := by
    have derivativeNormNonnegative := norm_nonneg
      (fderiv ℝ mapping first - ContinuousLinearMap.id ℝ Space)
    exact derivativeNormNonnegative.trans (derivativeClose first firstIn)
  nlinarith [meanValue', norm_nonneg (second - first),
    norm_nonneg (mapping second - mapping first)]

theorem injOn_of_fderiv_close_to_identity
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (mapping : Space → Space) (domain : Set Space) (domainConvex : Convex ℝ domain)
    (error : ℝ) (errorSmall : error < 1)
    (mappingDifferentiable : ∀ point ∈ domain,
      DifferentiableAt ℝ mapping point)
    (derivativeClose : ∀ point ∈ domain,
      ‖fderiv ℝ mapping point - ContinuousLinearMap.id ℝ Space‖ ≤ error) :
    Set.InjOn mapping domain := by
  intro first firstIn second secondIn equality
  have lower := one_sub_mul_norm_le_norm_image_sub_of_fderiv_close mapping
    domain domainConvex error mappingDifferentiable derivativeClose first firstIn
    second secondIn
  rw [equality, sub_self, norm_zero] at lower
  have factorPositive : 0 < 1 - error := sub_pos.mpr errorSmall
  have differenceZero : ‖second - first‖ = 0 := by
    nlinarith [norm_nonneg (second - first)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp differenceZero)).symm

end Grad.PhysicalFamily.SampledGlobalEmbedding
