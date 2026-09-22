import SampledAllTimeBounds
import SampledPositionDerivative
import GeometricSamplingThreshold

noncomputable section

open Set

namespace Grad.PhysicalFamily.SampledSeedBounds

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledAllTimeBounds
open Grad.PhysicalFamily.SampledSeminormBounds
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledPositionDerivative
open Grad.PhysicalFamily.GeometricSamplingThreshold
open Grad.GeometryClosure
open Grad.MainAssembly.SampledAxisBasics
open Matrix

noncomputable def planeEmbeddingLinearMap : Plane →ₗ[ℝ] Vec where
  toFun := planeEmbedding
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [planeEmbedding, vector]
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [planeEmbedding, vector]

noncomputable def planeEmbeddingCLM : Plane →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap planeEmbeddingLinearMap

@[simp] theorem planeEmbeddingCLM_apply (point : Plane) :
    planeEmbeddingCLM point = planeEmbedding point :=
  rfl

theorem planeEmbedding_norm (point : Plane) :
    ‖planeEmbedding point‖ = ‖point‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [planeEmbedding, vector, Fin.sum_univ_three, Fin.sum_univ_two]

theorem coordinatePoint_hasFDerivAt (point : Plane) (time : ℝ) :
    HasFDerivAt (fun argument : Plane => coordinatePoint argument time)
      planeEmbeddingCLM point := by
  let base : Vec := vector 0 time 0
  have derivative :=
    (hasFDerivAt_const (x := point) base).add planeEmbeddingCLM.hasFDerivAt
  have functionIdentity :
      (fun argument : Plane => coordinatePoint argument time) =
        (fun argument : Plane => base + planeEmbeddingCLM argument) := by
    funext argument
    ext coordinate
    fin_cases coordinate <;>
      simp [base, planeEmbeddingCLM_apply, planeEmbedding, coordinatePoint,
        vector]
  have derivative' : HasFDerivAt
      ((fun _ : Plane => base) + (planeEmbeddingCLM : Plane → Vec))
        planeEmbeddingCLM point :=
    derivative.congr_fderiv (zero_add planeEmbeddingCLM)
  apply derivative'.congr_of_eventuallyEq
  filter_upwards [] with argument
  exact congrFun functionIdentity argument

private def planeMatrixAction (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (point : Plane) : Plane :=
  WithLp.toLp 2 (matrix *ᵥ fun coordinate => point coordinate)

private theorem planeMatrixAction_mul
    (first second : Matrix (Fin 2) (Fin 2) ℝ) (point : Plane) :
    planeMatrixAction (first * second) point =
      planeMatrixAction first (planeMatrixAction second point) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [planeMatrixAction, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

private theorem planarRotation_norm_sq (angle : ℝ) (point : Plane) :
    ‖planeMatrixAction (planarRotation angle) point‖ ^ 2 = ‖point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [planeMatrixAction, planarRotation, dotProduct,
    Fin.sum_univ_two]
  nlinarith [Real.sin_sq_add_cos_sq angle]

private theorem diagonal_lower_norm_sq
    (rho : ℝ) (point : Plane) (rhoNonnegative : 0 ≤ rho)
    (rhoUpper : rho < 1) :
    (1 - rho) * ‖point‖ ^ 2 ≤
      ‖planeMatrixAction
        !![Real.sqrt (1 + rho), 0; 0, Real.sqrt (1 - rho)] point‖ ^ 2 := by
  have plusNonnegative : 0 ≤ 1 + rho := by linarith
  have minusNonnegative : 0 ≤ 1 - rho := by linarith
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [planeMatrixAction, dotProduct, Fin.sum_univ_two]
  calc
    (1 - rho) * (point 0 ^ 2 + point 1 ^ 2) ≤
        (1 + rho) * point 0 ^ 2 + (1 - rho) * point 1 ^ 2 := by
          nlinarith [sq_nonneg (point 0)]
    _ = (Real.sqrt (1 + rho) * point 0) ^ 2 +
        (Real.sqrt (1 - rho) * point 1) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt plusNonnegative,
            Real.sq_sqrt minusNonnegative]

/-- The squared norm of the harmonic seed is bounded below uniformly in its
angle and in the cell parameter.  The constant is the smaller diagonal
eigenvalue and is independent of time. -/
theorem one_sub_rho_mul_norm_sq_le_seedAction_norm_sq
    (rho alpha delta parameter time : ℝ) (point : Plane)
    (rhoNonnegative : 0 ≤ rho) (rhoUpper : rho < 1) :
    (1 - rho) * ‖point‖ ^ 2 ≤
      ‖seedAction rho alpha delta parameter time point‖ ^ 2 := by
  let angle := seedAngle alpha delta parameter time
  let rotatedPoint := planeMatrixAction (planarRotation (-angle)) point
  have seedIdentity :
      seedAction rho alpha delta parameter time point =
        planeMatrixAction (planarRotation angle)
          (planeMatrixAction
            !![Real.sqrt (1 + rho), 0; 0, Real.sqrt (1 - rho)]
            rotatedPoint) := by
    change planeMatrixAction (harmonicSeedMatrix rho alpha delta parameter time)
        point = _
    rw [harmonicSeedMatrix_formula]
    rw [planeMatrixAction_mul, planeMatrixAction_mul]
  rw [seedIdentity, planarRotation_norm_sq]
  calc
    (1 - rho) * ‖point‖ ^ 2 =
        (1 - rho) * ‖rotatedPoint‖ ^ 2 := by
          simp only [rotatedPoint, planarRotation_norm_sq]
    _ ≤ _ := diagonal_lower_norm_sq rho rotatedPoint rhoNonnegative rhoUpper

theorem sqrt_one_sub_rho_mul_norm_le_seedAction_norm
    (rho alpha delta parameter time : ℝ) (point : Plane)
    (rhoNonnegative : 0 ≤ rho) (rhoUpper : rho < 1) :
    Real.sqrt (1 - rho) * ‖point‖ ≤
      ‖seedAction rho alpha delta parameter time point‖ := by
  apply (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - rho)]
  exact one_sub_rho_mul_norm_sq_le_seedAction_norm_sq rho alpha delta
    parameter time point rhoNonnegative rhoUpper

/-- The normal-plane part of the axis map is orthogonal to its tilt part, so
the tilt can only increase the output norm. -/
theorem seed_component_norm_le_cellAxisCLM_norm
    (rho alpha delta parameter time a : ℝ) (tilt point : Plane)
    (aNonnegative : 0 ≤ a) :
    a * ‖seedAction rho alpha delta parameter time point‖ ≤
      ‖cellAxisCLM rho alpha delta parameter time a tilt point‖ := by
  apply (sq_le_sq₀
    (mul_nonneg aNonnegative (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [cellAxisCLM_apply, planeEmbedding, tangentDirection, basisVector,
    vector, Fin.sum_univ_three, Fin.sum_univ_two, smul_eq_mul]
  nlinarith [sq_nonneg (planeDot tilt point)]

theorem axis_lower_mul_norm_le_cellAxisCLM_norm
    (rho alpha delta parameter time a : ℝ) (tilt point : Plane)
    (rhoNonnegative : 0 ≤ rho) (rhoUpper : rho < 1)
    (aNonnegative : 0 ≤ a) :
    (a * Real.sqrt (1 - rho)) * ‖point‖ ≤
      ‖cellAxisCLM rho alpha delta parameter time a tilt point‖ := by
  calc
    (a * Real.sqrt (1 - rho)) * ‖point‖ =
        a * (Real.sqrt (1 - rho) * ‖point‖) := by ring
    _ ≤ a * ‖seedAction rho alpha delta parameter time point‖ :=
      mul_le_mul_of_nonneg_left
        (sqrt_one_sub_rho_mul_norm_le_seedAction_norm rho alpha delta
          parameter time point rhoNonnegative rhoUpper) aNonnegative
    _ ≤ _ := seed_component_norm_le_cellAxisCLM_norm rho alpha delta
      parameter time a tilt point aNonnegative

/-- The exact disk derivative of the remainder is uniformly small at every
real cell time, including boundary points of the closed disk. -/
theorem remainder_disk_fderiv_apply_norm_le_physicalBound_allTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (direction : Plane) :
    ‖fderiv ℝ
        (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point
        direction‖ ≤
      (family.bound * |epsilon|) * ‖direction‖ := by
  let reducedTime := fundamentalTime time
  rw [remainder_disk_fderiv_eq_fundamentalTime cellLength family epsilon
    epsilonIn parameter point pointIn time]
  let jointRemainder : Vec → Vec := fun argument =>
    family.remainder epsilon parameter.val (coordinateDisk argument)
      (argument 1)
  let insertion : Vec → CellArgument := fun argument =>
    (epsilon, (parameter.val, argument))
  have coordinateIn : coordinatePoint point reducedTime ∈
      coordinateCollar family.collarRadius := by
    change ‖coordinateDisk (coordinatePoint point reducedTime)‖ <
      family.collarRadius
    rw [coordinateDisk_coordinatePoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have inputIn : insertion (coordinatePoint point reducedTime) ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) :=
    ⟨epsilonIn, parameter_mem_open cellLength family parameter, coordinateIn⟩
  have domainOpen : IsOpen
      (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius)) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod
      (coordinateCollar_isOpen family.collarRadius))
  have insertionDifferentiable : DifferentiableAt ℝ insertion
      (coordinatePoint point reducedTime) := by
    dsimp [insertion]
    fun_prop
  have outerDifferentiable : DifferentiableAt ℝ
      (uncurriedCell family.remainder)
      (insertion (coordinatePoint point reducedTime)) :=
    (family.remainderSmooth.contDiffAt (domainOpen.mem_nhds inputIn))
      |>.differentiableAt (by simp)
  have jointDifferentiable : DifferentiableAt ℝ jointRemainder
      (coordinatePoint point reducedTime) := by
    have composed := outerDifferentiable.comp
      (coordinatePoint point reducedTime) insertionDifferentiable
    simpa [Function.comp_def, uncurriedCell, insertion, jointRemainder] using
      composed
  have chain := fderiv_comp (x := point) jointDifferentiable
    (coordinatePoint_hasFDerivAt point reducedTime).differentiableAt
  rw [(coordinatePoint_hasFDerivAt point reducedTime).fderiv] at chain
  have diskDerivative :
      fderiv ℝ
          (fun argument : Plane => family.remainder epsilon parameter.val
            argument reducedTime) point =
        (fderiv ℝ jointRemainder (coordinatePoint point reducedTime)).comp
          planeEmbeddingCLM := by
    simpa [Function.comp_def, jointRemainder] using chain
  rw [diskDerivative]
  have jointBound :
      ‖fderiv ℝ jointRemainder (coordinatePoint point reducedTime)‖ ≤
        family.bound * |epsilon| := by
    have bound := remainder_iteratedFDeriv_le_physicalBound cellLength family
      epsilon epsilonIn parameter (⟨1, by omega⟩ : Fin 3) point pointIn reducedTime
      ⟨(fundamentalTime_mem_Ico time).1,
        (fundamentalTime_mem_Ico time).2.le⟩
    change ‖iteratedFDeriv ℝ 1 jointRemainder
      (coordinatePoint point reducedTime)‖ ≤ family.bound * |epsilon| at bound
    simpa only [norm_iteratedFDeriv_one] using bound
  calc
    ‖((fderiv ℝ jointRemainder (coordinatePoint point reducedTime)).comp
        planeEmbeddingCLM) direction‖ =
        ‖fderiv ℝ jointRemainder (coordinatePoint point reducedTime)
          (planeEmbedding direction)‖ := rfl
    _ ≤ ‖fderiv ℝ jointRemainder (coordinatePoint point reducedTime)‖ *
        ‖planeEmbedding direction‖ :=
      (fderiv ℝ jointRemainder (coordinatePoint point reducedTime)).le_opNorm _
    _ = ‖fderiv ℝ jointRemainder (coordinatePoint point reducedTime)‖ *
        ‖direction‖ := by rw [planeEmbedding_norm]
    _ ≤ (family.bound * |epsilon|) * ‖direction‖ :=
      mul_le_mul_of_nonneg_right jointBound (norm_nonneg direction)

/-- A quantitative seed-versus-remainder gap makes the exact disk derivative
injective at every point of the closed disk and every real cell time. -/
theorem v_disk_fderiv_injective_of_error_lt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (errorSmall : family.bound * |epsilon| <
      normalizedFactor (family.tilt epsilon parameter.val time) *
        Real.sqrt (1 - family.rho)) :
    Function.Injective
      (fderiv ℝ (fun argument : Plane =>
        family.v epsilon parameter.val argument time) point) := by
  let factor := normalizedFactor (family.tilt epsilon parameter.val time)
  let axisMap := cellAxisCLM family.rho family.alpha family.delta
    parameter.val time factor (family.tilt epsilon parameter.val time)
  let remainderMap := fderiv ℝ (fun argument : Plane =>
    family.remainder epsilon parameter.val argument time) point
  have factorNonnegative : 0 ≤ factor := Real.sqrt_nonneg _
  intro first second equality
  let difference := first - second
  have totalZero :
      fderiv ℝ (fun argument : Plane =>
        family.v epsilon parameter.val argument time) point difference = 0 := by
    dsimp [difference]
    rw [map_sub, equality, sub_self]
  rw [v_fderiv_closedDisk_eq_axis_add_remainder cellLength family epsilon
    epsilonIn parameter time point pointIn] at totalZero
  change axisMap difference + remainderMap difference = 0 at totalZero
  have axisEquality : axisMap difference = -remainderMap difference :=
    eq_neg_of_add_eq_zero_left totalZero
  have normEquality : ‖axisMap difference‖ = ‖remainderMap difference‖ := by
    rw [axisEquality, norm_neg]
  have lower :
      (factor * Real.sqrt (1 - family.rho)) * ‖difference‖ ≤
        ‖axisMap difference‖ := by
    exact axis_lower_mul_norm_le_cellAxisCLM_norm family.rho family.alpha
      family.delta parameter.val time factor
      (family.tilt epsilon parameter.val time) difference
      family.rhoPositive.le (by linarith [family.rhoSmall]) factorNonnegative
  have upper : ‖remainderMap difference‖ ≤
      (family.bound * |epsilon|) * ‖difference‖ := by
    exact remainder_disk_fderiv_apply_norm_le_physicalBound_allTime
      cellLength family epsilon epsilonIn parameter point pointIn time difference
  have differenceZero : difference = 0 := by
    by_contra nonzero
    have normPositive : 0 < ‖difference‖ := norm_pos_iff.mpr nonzero
    have strictGap :
        (family.bound * |epsilon|) * ‖difference‖ <
          (factor * Real.sqrt (1 - family.rho)) * ‖difference‖ :=
      mul_lt_mul_of_pos_right (by simpa [factor] using errorSmall) normPositive
    linarith [lower, upper, normEquality]
  exact sub_eq_zero.mp differenceZero

/-- One integer threshold makes the exact cell disk derivative injective at
every parameter, every point of the closed disk, and every real cell time. -/
theorem exists_diskDerivativeSamplingThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈
          Set.Ioo (-family.epsilonZero) family.epsilonZero ∧
        ∀ (parameter : Set.Icc family.lower family.upper)
          (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
          Function.Injective
            (fderiv ℝ (fun argument : Plane =>
              family.v (sampledEpsilon period) parameter.val argument time)
              point) := by
  obtain ⟨firstPeriod, firstPositive, threshold⟩ :=
    exists_geometricSamplingThreshold cellLength cellLengthPositive family
      (1 / 4) (by norm_num) 0
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter
  obtain ⟨epsilonIn, errorSmall, _radiusLarge⟩ := threshold period periodAfter
  refine ⟨epsilonIn, ?_⟩
  intro parameter point pointIn time
  let error := family.bound * |sampledEpsilon period|
  let factor := normalizedFactor
    (family.tilt (sampledEpsilon period) parameter.val time)
  have errorNonnegative : 0 ≤ error :=
    mul_nonneg (by linarith [family.boundAtLeastOne]) (abs_nonneg _)
  have factorCloseness : |factor - 1| ≤ error ^ 2 / 2 := by
    simpa [factor, error] using
      abs_normalizedFactor_sub_one_le_physicalBound_allTime cellLength family
        (sampledEpsilon period) epsilonIn parameter time
  have factorLower : (1 / 2 : ℝ) < factor := by
    have lowerDifference := (abs_le.mp factorCloseness).1
    have errorUpper : error < 1 / 4 := by simpa [error] using errorSmall
    nlinarith [sq_nonneg error]
  have sqrtLower : (1 / 2 : ℝ) < Real.sqrt (1 - family.rho) := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by linarith [family.rhoSmall])]
    nlinarith [family.rhoSmall]
  have productLower : (1 / 4 : ℝ) <
      factor * Real.sqrt (1 - family.rho) := by
    have firstStep : (1 / 4 : ℝ) <
        (1 / 2) * Real.sqrt (1 - family.rho) := by
      have scaled := mul_lt_mul_of_pos_left sqrtLower
        (by norm_num : (0 : ℝ) < 1 / 2)
      norm_num at scaled ⊢
      exact scaled
    have secondStep :
        (1 / 2) * Real.sqrt (1 - family.rho) <
          factor * Real.sqrt (1 - family.rho) :=
      mul_lt_mul_of_pos_right factorLower
        (lt_trans (by norm_num) sqrtLower)
    exact firstStep.trans secondStep
  apply v_disk_fderiv_injective_of_error_lt cellLength family
    (sampledEpsilon period) epsilonIn parameter point pointIn time
  exact (by simpa [error, factor] using errorSmall.trans productLower)

end Grad.PhysicalFamily.SampledSeedBounds
