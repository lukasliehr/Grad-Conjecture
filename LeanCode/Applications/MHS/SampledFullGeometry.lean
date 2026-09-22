import SampledSeedBounds

noncomputable section

open Set Filter
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledFullGeometry

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledAllTimeBounds
open Grad.PhysicalFamily.SampledSeminormBounds.Consumer
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledPositionDerivative
open Grad.PhysicalFamily.SampledSeedBounds
open Grad.PhysicalFamily.SampledNormalizedFactorBounds
open Grad.PhysicalFamily.GeometricSamplingThreshold
open Grad.MainAssembly.SampledAxisBasics
open Grad.MainAssembly.PhysicalNormalHessian
open Matrix

private theorem fderiv_periodic_of_contDiff
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (mapping : ℝ → Target) (period : ℝ)
    (smooth : ContDiff ℝ ∞ mapping)
    (periodic : Function.Periodic mapping period) :
    Function.Periodic (fun time => fderiv ℝ mapping time) period := by
  intro time
  have mappingDifferentiable : DifferentiableAt ℝ mapping (time + period) :=
    (smooth.differentiable (by simp)).differentiableAt
  have shiftDifferentiable : DifferentiableAt ℝ (fun offset : ℝ =>
      offset + period) time := by
    fun_prop
  have chain := fderiv_comp (x := time) mappingDifferentiable
    shiftDifferentiable
  have shiftedFunction : (fun offset : ℝ => mapping (offset + period)) =
      mapping := by
    funext offset
    exact periodic offset
  change fderiv ℝ (fun offset : ℝ => mapping (offset + period)) time = _
    at chain
  rw [shiftedFunction] at chain
  symm
  change fderiv ℝ mapping time = fderiv ℝ mapping (time + period)
  simpa using chain

theorem remainder_time_contDiff
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    ContDiff ℝ ∞ (family.remainder epsilon parameter.val point) := by
  let insertion : ℝ → CellArgument := fun time =>
    (epsilon, (parameter.val, coordinatePoint point time))
  have insertionSmooth : ContDiff ℝ ∞ insertion := by
    have coordinateSmooth : ContDiff ℝ ∞
        (fun time : ℝ => coordinatePoint point time) :=
      coordinatePoint_uncurried_contDiff.comp
        (contDiff_const.prodMk contDiff_id)
    exact contDiff_const.prodMk (contDiff_const.prodMk coordinateSmooth)
  rw [contDiff_iff_contDiffAt]
  intro time
  have inputIn : insertion time ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) := by
    refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
    change ‖coordinateDisk (coordinatePoint point time)‖ < family.collarRadius
    rw [coordinateDisk_coordinatePoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have domainOpen : IsOpen
      (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius)) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod
      (coordinateCollar_isOpen family.collarRadius))
  have outer := family.remainderSmooth.contDiffAt
    (domainOpen.mem_nhds inputIn)
  simpa [Function.comp_def, insertion, uncurriedCell] using
    outer.comp time insertionSmooth.contDiffAt

theorem tilt_time_contDiff
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) :
    ContDiff ℝ ∞ (family.tilt epsilon parameter.val) := by
  let insertion : ℝ → CircleArgument := fun time =>
    (epsilon, (parameter.val, time))
  have insertionSmooth : ContDiff ℝ ∞ insertion := by
    dsimp [insertion]
    fun_prop
  rw [contDiff_iff_contDiffAt]
  intro time
  have inputIn : insertion time ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ Set.univ) :=
    ⟨epsilonIn, parameter_mem_open cellLength family parameter,
      Set.mem_univ time⟩
  have domainOpen : IsOpen
      (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ Set.univ)) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod
      (isOpen_univ : IsOpen (Set.univ : Set ℝ)))
  have outer := family.tiltSmooth.contDiffAt
    (domainOpen.mem_nhds inputIn)
  simpa [Function.comp_def, insertion, uncurriedCircle] using
    outer.comp time insertionSmooth.contDiffAt

theorem remainder_time_fderiv_periodic
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    Function.Periodic
      (fun time => fderiv ℝ
        (family.remainder epsilon parameter.val point) time)
      (2 * Real.pi) := by
  apply fderiv_periodic_of_contDiff
    (smooth := remainder_time_contDiff cellLength family epsilon epsilonIn
      parameter point pointIn)
  exact family.remainderPeriodic epsilon epsilonIn parameter.val
    (parameter_mem_open cellLength family parameter) point
    (closed_disk_mem_collar cellLength family point pointIn)

theorem tilt_time_fderiv_periodic
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) :
    Function.Periodic
      (fun time => fderiv ℝ (family.tilt epsilon parameter.val) time)
      (2 * Real.pi) := by
  apply fderiv_periodic_of_contDiff
    (smooth := tilt_time_contDiff cellLength family epsilon epsilonIn parameter)
  exact family.tiltPeriodic epsilon epsilonIn parameter.val
    (parameter_mem_open cellLength family parameter)

noncomputable def cellTimeLinearMap : ℝ →ₗ[ℝ] Vec where
  toFun scalar := scalar • basisVector 1
  map_add' first second := by simp [add_smul]
  map_smul' scalar value := by simp [mul_smul]

noncomputable def cellTimeCLM : ℝ →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap cellTimeLinearMap

@[simp] theorem cellTimeCLM_apply (scalar : ℝ) :
    cellTimeCLM scalar = scalar • basisVector 1 := rfl

theorem basisVector_one_norm : ‖basisVector 1‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [basisVector]

noncomputable def cellArgumentTimeLinearMap : ℝ →ₗ[ℝ] CellArgument where
  toFun scalar := (0, (0, scalar • tangentDirection))
  map_add' first second := by simp [add_smul]
  map_smul' scalar value := by simp [mul_smul]

noncomputable def cellArgumentTimeCLM : ℝ →L[ℝ] CellArgument :=
  LinearMap.toContinuousLinearMap cellArgumentTimeLinearMap

@[simp] theorem cellArgumentTimeCLM_apply (scalar : ℝ) :
    cellArgumentTimeCLM scalar =
      (0, (0, scalar • tangentDirection)) := rfl

private def compactCellArguments
    (family : CellSolutionFamily cellLength) : Set CellArgument :=
  Set.Icc (-family.epsilonZero / 2) (family.epsilonZero / 2) ×ˢ
    (Set.Icc family.lower family.upper ×ˢ
      ((fun argument : Plane × ℝ =>
          coordinatePoint argument.1 argument.2) ''
        (Metric.closedBall (0 : Plane) 1 ×ˢ
          Set.Icc (0 : ℝ) (2 * Real.pi))))

private theorem compactCellArguments_isCompact
    (family : CellSolutionFamily cellLength) :
    IsCompact (compactCellArguments family) := by
  exact isCompact_Icc.prod (isCompact_Icc.prod
    ((isCompact_closedBall (0 : Plane) 1).prod isCompact_Icc |>.image
      coordinatePoint_uncurried_contDiff.continuous))

private theorem compactCellArguments_subset_smoothDomain
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    compactCellArguments family ⊆
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) := by
  rintro ⟨epsilon, ⟨parameter, point⟩⟩
    ⟨epsilonIn, parameterIn, ⟨⟨disk, time⟩, ⟨diskIn, _⟩, rfl⟩⟩
  have epsilonPositive := family.epsilonPositive
  have diskNorm : ‖disk‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using diskIn
  refine ⟨⟨by linarith [epsilonIn.1], by linarith [epsilonIn.2]⟩, ?_⟩
  refine ⟨⟨lt_of_lt_of_le family.parameterContains.1 parameterIn.1,
    lt_of_le_of_lt parameterIn.2 family.parameterContains.2⟩, ?_⟩
  change ‖coordinateDisk (coordinatePoint disk time)‖ <
      family.collarRadius
  rw [coordinateDisk_coordinatePoint]
  exact lt_of_le_of_lt diskNorm family.collarLarge

private theorem exists_jointV_fderiv_norm_bound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, ∀ argument ∈ compactCellArguments family,
      ‖fderiv ℝ (uncurriedCell family.v) argument‖ ≤ bound := by
  have derivativeContinuous : ContinuousOn
      (iteratedFDeriv ℝ 1 (uncurriedCell family.v))
      (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius)) :=
    ContinuousOn.continuousOn_iteratedFDeriv family.vSmooth
      (isOpen_Ioo.prod (isOpen_Ioo.prod
        (coordinateCollar_isOpen family.collarRadius)))
      (show (1 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have normContinuous : ContinuousOn
      (fun argument =>
        ‖iteratedFDeriv ℝ 1 (uncurriedCell family.v) argument‖)
      (compactCellArguments family) :=
    (derivativeContinuous.mono
      (compactCellArguments_subset_smoothDomain cellLength family)).norm
  obtain ⟨bound, boundUpper⟩ :=
    (compactCellArguments_isCompact family).bddAbove_image normContinuous
  refine ⟨bound, ?_⟩
  intro argument argumentIn
  have upper := boundUpper ⟨argument, argumentIn, rfl⟩
  simpa only [norm_iteratedFDeriv_one] using upper

theorem remainder_time_fderiv_apply_norm_le_physicalBound_allTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time direction : ℝ) :
    ‖fderiv ℝ (family.remainder epsilon parameter.val point) time direction‖ ≤
      (family.bound * |epsilon|) * ‖direction‖ := by
  rw [periodic_eq_fundamentalTime _
    (remainder_time_fderiv_periodic cellLength family epsilon epsilonIn
      parameter point pointIn) time]
  let reducedTime := fundamentalTime time
  let jointRemainder : Vec → Vec := fun argument =>
    family.remainder epsilon parameter.val (coordinateDisk argument)
      (argument 1)
  have jointDifferentiable : DifferentiableAt ℝ jointRemainder
      (coordinatePoint point reducedTime) := by
    let insertion : Vec → CellArgument := fun argument =>
      (epsilon, (parameter.val, argument))
    have inputIn : insertion (coordinatePoint point reducedTime) ∈
        Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
          (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
            coordinateCollar family.collarRadius) := by
      refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
      change ‖coordinateDisk (coordinatePoint point reducedTime)‖ <
        family.collarRadius
      rw [coordinateDisk_coordinatePoint]
      exact lt_of_le_of_lt pointIn family.collarLarge
    have domainOpen : IsOpen
        (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
          (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
            coordinateCollar family.collarRadius)) :=
      isOpen_Ioo.prod (isOpen_Ioo.prod
        (coordinateCollar_isOpen family.collarRadius))
    have outer := family.remainderSmooth.contDiffAt
      (domainOpen.mem_nhds inputIn) |>.differentiableAt (by simp)
    have insertionDifferentiable : DifferentiableAt ℝ insertion
        (coordinatePoint point reducedTime) := by
      dsimp [insertion]
      fun_prop
    simpa [Function.comp_def, insertion, uncurriedCell, jointRemainder] using
      outer.comp (coordinatePoint point reducedTime) insertionDifferentiable
  have timeSectionHasDerivative : HasFDerivAt
      (fun current : ℝ => coordinatePoint point current) cellTimeCLM
      reducedTime := by
    have derivative := (hasFDerivAt_const (x := reducedTime)
      (coordinatePoint point 0)).add cellTimeCLM.hasFDerivAt
    have functionIdentity :
        (fun current : ℝ => coordinatePoint point current) =
          (fun current : ℝ =>
            coordinatePoint point 0 + cellTimeCLM current) := by
      funext current
      ext coordinate
      fin_cases coordinate <;>
        simp [cellTimeCLM_apply, coordinatePoint, basisVector, vector]
    have derivative' : HasFDerivAt
        ((fun _ : ℝ => coordinatePoint point 0) + (cellTimeCLM : ℝ → Vec))
        cellTimeCLM reducedTime :=
      derivative.congr_fderiv (zero_add cellTimeCLM)
    apply derivative'.congr_of_eventuallyEq
    filter_upwards [] with current
    exact congrFun functionIdentity current
  have chain := fderiv_comp (x := reducedTime) jointDifferentiable
    timeSectionHasDerivative.differentiableAt
  rw [timeSectionHasDerivative.fderiv] at chain
  have compositionIdentity : jointRemainder ∘
      (fun current : ℝ => coordinatePoint point current) =
      family.remainder epsilon parameter.val point := by
    funext current
    simp [jointRemainder]
  rw [compositionIdentity] at chain
  have evaluated := congrArg (fun derivative : ℝ →L[ℝ] Vec =>
    derivative direction) chain
  rw [evaluated]
  calc
    ‖fderiv ℝ jointRemainder (coordinatePoint point reducedTime)
        (cellTimeCLM direction)‖ ≤
        ‖fderiv ℝ jointRemainder (coordinatePoint point reducedTime)‖ *
          ‖cellTimeCLM direction‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (family.bound * |epsilon|) * ‖cellTimeCLM direction‖ :=
      mul_le_mul_of_nonneg_right
        (remainder_fderiv_norm_le_physicalBound cellLength family epsilon
          epsilonIn parameter point pointIn reducedTime
          ⟨(fundamentalTime_mem_Ico time).1,
            (fundamentalTime_mem_Ico time).2.le⟩)
        (norm_nonneg _)
    _ = (family.bound * |epsilon|) * ‖direction‖ := by
      rw [cellTimeCLM_apply, norm_smul, basisVector_one_norm]
      simp [Real.norm_eq_abs]

theorem tilt_time_fderiv_apply_norm_le_physicalBound_allTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (time direction : ℝ) :
    ‖fderiv ℝ (family.tilt epsilon parameter.val) time direction‖ ≤
      (family.bound * |epsilon|) * ‖direction‖ := by
  rw [periodic_eq_fundamentalTime _
    (tilt_time_fderiv_periodic cellLength family epsilon epsilonIn parameter)
    time]
  exact ContinuousLinearMap.le_of_opNorm_le
    (f := fderiv ℝ (family.tilt epsilon parameter.val)
      (fundamentalTime time))
    (tilt_fderiv_norm_le_physicalBound cellLength family epsilon epsilonIn
      parameter (fundamentalTime time)
      ⟨(fundamentalTime_mem_Ico time).1,
        (fundamentalTime_mem_Ico time).2.le⟩) direction

theorem coordinate_abs_le_norm (point : Vec) (coordinate : Fin 3) :
    |point coordinate| ≤ ‖point‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, EuclideanSpace.real_norm_sq_eq]
  fin_cases coordinate <;>
    simp [Fin.sum_univ_three] <;>
    nlinarith [sq_nonneg (point 0), sq_nonneg (point 1), sq_nonneg (point 2)]

theorem coordinateDisk_norm_le (point : Vec) :
    ‖coordinateDisk point‖ ≤ ‖point‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [coordinateDisk, Fin.sum_univ_two, Fin.sum_univ_three]
  exact sq_nonneg (point 1)

theorem abs_planeDot_le_norm_mul_norm (first second : Plane) :
    |planeDot first second| ≤ ‖first‖ * ‖second‖ := by
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [sq_abs, mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [planeDot, Fin.sum_univ_two]
  nlinarith [sq_nonneg
    (first 0 * second 1 - first 1 * second 0)]

theorem v_disk_fderiv_coordinate_one
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (direction : Plane) :
    (fderiv ℝ (fun argument : Plane =>
      family.v epsilon parameter.val argument time) point direction) 1 =
      planeDot (family.tilt epsilon parameter.val time) direction +
        (fderiv ℝ (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point
          direction) 1 := by
  have derivativeEquality := v_fderiv_closedDisk_eq_axis_add_remainder
    cellLength family epsilon epsilonIn parameter time point pointIn
  have evaluated := congrArg (fun derivative : Plane →L[ℝ] Vec =>
    (derivative direction) 1) derivativeEquality
  simpa [cellAxisCLM_apply, planeEmbedding, tangentDirection, basisVector,
    vector] using evaluated

theorem abs_v_disk_fderiv_coordinate_one_le
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (direction : Plane) :
    |(fderiv ℝ (fun argument : Plane =>
      family.v epsilon parameter.val argument time) point direction) 1| ≤
      (2 * (family.bound * |epsilon|)) * ‖direction‖ := by
  rw [v_disk_fderiv_coordinate_one cellLength family epsilon epsilonIn
    parameter point pointIn time direction]
  calc
    |planeDot (family.tilt epsilon parameter.val time) direction +
        (fderiv ℝ (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point
          direction) 1| ≤
        |planeDot (family.tilt epsilon parameter.val time) direction| +
          |(fderiv ℝ (fun argument : Plane =>
            family.remainder epsilon parameter.val argument time) point
          direction) 1| := abs_add_le _ _
    _ ≤ ‖family.tilt epsilon parameter.val time‖ * ‖direction‖ +
          ‖fderiv ℝ (fun argument : Plane =>
            family.remainder epsilon parameter.val argument time) point
            direction‖ :=
      add_le_add (abs_planeDot_le_norm_mul_norm _ _)
        (coordinate_abs_le_norm _ 1)
    _ ≤ (family.bound * |epsilon|) * ‖direction‖ +
          (family.bound * |epsilon|) * ‖direction‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (tilt_value_norm_le_physicalBound_allTime cellLength family epsilon
            epsilonIn parameter time) (norm_nonneg _))
        (remainder_disk_fderiv_apply_norm_le_physicalBound_allTime
          cellLength family epsilon epsilonIn parameter point pointIn time
          direction)
    _ = (2 * (family.bound * |epsilon|)) * ‖direction‖ := by ring

theorem coordinateDisk_v_disk_fderiv_lower
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (direction : Plane) :
    ((normalizedFactor (family.tilt epsilon parameter.val time) *
        Real.sqrt (1 - family.rho)) - family.bound * |epsilon|) *
        ‖direction‖ ≤
      ‖coordinateDisk (fderiv ℝ (fun argument : Plane =>
        family.v epsilon parameter.val argument time) point direction)‖ := by
  have derivativeEquality := v_fderiv_closedDisk_eq_axis_add_remainder
    cellLength family epsilon epsilonIn parameter time point pointIn
  have evaluated := congrArg (fun derivative : Plane →L[ℝ] Vec =>
    coordinateDisk (derivative direction)) derivativeEquality
  have diskEquality :
      coordinateDisk (fderiv ℝ (fun argument : Plane =>
        family.v epsilon parameter.val argument time) point direction) =
        normalizedFactor (family.tilt epsilon parameter.val time) •
          seedAction family.rho family.alpha family.delta parameter.val time
            direction +
        coordinateDisk (fderiv ℝ (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point
          direction) := by
    rw [evaluated]
    ext coordinate
    fin_cases coordinate <;>
      simp [cellAxisCLM_apply, planeEmbedding, tangentDirection, basisVector,
        coordinateDisk, vector]
  rw [diskEquality]
  have seedLower := sqrt_one_sub_rho_mul_norm_le_seedAction_norm
    family.rho family.alpha family.delta parameter.val time direction
    family.rhoPositive.le (by linarith [family.rhoSmall] : family.rho < 1)
  have factorNonnegative := normalizedFactor_nonnegative
    (family.tilt epsilon parameter.val time)
  have mainLower :
      (normalizedFactor (family.tilt epsilon parameter.val time) *
        Real.sqrt (1 - family.rho)) * ‖direction‖ ≤
      ‖normalizedFactor (family.tilt epsilon parameter.val time) •
        seedAction family.rho family.alpha family.delta parameter.val time
          direction‖ := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg factorNonnegative]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left seedLower factorNonnegative)
  have errorUpper :
      ‖coordinateDisk (fderiv ℝ (fun argument : Plane =>
        family.remainder epsilon parameter.val argument time) point
        direction)‖ ≤ (family.bound * |epsilon|) * ‖direction‖ :=
    (coordinateDisk_norm_le _).trans
      (remainder_disk_fderiv_apply_norm_le_physicalBound_allTime
        cellLength family epsilon epsilonIn parameter point pointIn time
        direction)
  calc
    ((normalizedFactor (family.tilt epsilon parameter.val time) *
        Real.sqrt (1 - family.rho)) - family.bound * |epsilon|) *
        ‖direction‖ =
      (normalizedFactor (family.tilt epsilon parameter.val time) *
        Real.sqrt (1 - family.rho)) * ‖direction‖ -
          (family.bound * |epsilon|) * ‖direction‖ := by ring
    _ ≤ ‖normalizedFactor (family.tilt epsilon parameter.val time) •
          seedAction family.rho family.alpha family.delta parameter.val time
            direction‖ -
        ‖coordinateDisk (fderiv ℝ (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point
          direction)‖ := sub_le_sub mainLower errorUpper
    _ ≤ ‖normalizedFactor (family.tilt epsilon parameter.val time) •
          seedAction family.rho family.alpha family.delta parameter.val time
            direction +
        coordinateDisk (fderiv ℝ (fun argument : Plane =>
          family.remainder epsilon parameter.val argument time) point
          direction)‖ := by
      simpa only [norm_neg, sub_neg_eq_add] using
        (norm_sub_norm_le
          (normalizedFactor (family.tilt epsilon parameter.val time) •
            seedAction family.rho family.alpha family.delta parameter.val time
              direction)
          (-coordinateDisk (fderiv ℝ (fun argument : Plane =>
            family.remainder epsilon parameter.val argument time) point
            direction)))

/-- Under the fixed small-error regime, the exact disk derivative has a
uniform quantitative lower bound in the ambient physical norm. -/
theorem eighth_mul_norm_le_v_disk_fderiv
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (errorSmall : family.bound * |epsilon| < 1 / 16) (direction : Plane) :
    (1 / 8 : ℝ) * ‖direction‖ ≤
      ‖fderiv ℝ (fun argument : Plane =>
        family.v epsilon parameter.val argument time) point direction‖ := by
  let error := family.bound * |epsilon|
  let factor := normalizedFactor (family.tilt epsilon parameter.val time)
  have errorNonnegative : 0 ≤ error :=
    mul_nonneg (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _)
  have factorCloseness : |factor - 1| ≤ error ^ 2 / 2 := by
    simpa [factor, error] using
      abs_normalizedFactor_sub_one_le_physicalBound_allTime cellLength family
        epsilon epsilonIn parameter time
  have factorLower : (1 / 2 : ℝ) < factor := by
    have lowerDifference := (abs_le.mp factorCloseness).1
    have errorUpper : error < 1 / 16 := by simpa [error] using errorSmall
    nlinarith [sq_nonneg error]
  have sqrtLower : (1 / 2 : ℝ) < Real.sqrt (1 - family.rho) := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by linarith [family.rhoSmall])]
    nlinarith [family.rhoSmall]
  have coefficientLower : (1 / 8 : ℝ) <
      factor * Real.sqrt (1 - family.rho) - error := by
    have productLower : (1 / 4 : ℝ) <
        factor * Real.sqrt (1 - family.rho) := by
      nlinarith [mul_pos (sub_pos.mpr factorLower)
        (sub_pos.mpr sqrtLower)]
    have errorUpper : error < 1 / 16 := by simpa [error] using errorSmall
    linarith
  have planarLower := coordinateDisk_v_disk_fderiv_lower cellLength family
    epsilon epsilonIn parameter point pointIn time direction
  have planarToAmbient := coordinateDisk_norm_le
    (fderiv ℝ (fun argument : Plane =>
      family.v epsilon parameter.val argument time) point direction)
  have scaled := mul_le_mul_of_nonneg_right coefficientLower.le
    (norm_nonneg direction)
  have planarLower' :
      (factor * Real.sqrt (1 - family.rho) - error) * ‖direction‖ ≤
        ‖coordinateDisk (fderiv ℝ (fun argument : Plane =>
          family.v epsilon parameter.val argument time) point direction)‖ := by
    simpa [factor, error] using planarLower
  exact scaled.trans (planarLower'.trans planarToAmbient)

noncomputable def planeDotLinearMap (point : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun direction := planeDot direction point
  map_add' first second := by
    simp [planeDot]
    ring
  map_smul' scalar direction := by
    simp [planeDot]
    ring

noncomputable def planeDotCLM (point : Plane) : Plane →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (planeDotLinearMap point)

@[simp] theorem planeDotCLM_apply (point direction : Plane) :
    planeDotCLM point direction = planeDot direction point := rfl

noncomputable def vecCoordinateCLM (coordinate : Fin 3) : Vec →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) coordinate

@[simp] theorem vecCoordinateCLM_apply (coordinate : Fin 3) (point : Vec) :
    vecCoordinateCLM coordinate point = point coordinate := rfl

theorem v_time_contDiff
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    ContDiff ℝ ∞ (family.v epsilon parameter.val point) := by
  let insertion : ℝ → CellArgument := fun time =>
    (epsilon, (parameter.val, coordinatePoint point time))
  have coordinateSmooth : ContDiff ℝ ∞
      (fun time : ℝ => coordinatePoint point time) :=
    coordinatePoint_uncurried_contDiff.comp
      (contDiff_const.prodMk contDiff_id)
  have insertionSmooth : ContDiff ℝ ∞ insertion :=
    contDiff_const.prodMk (contDiff_const.prodMk coordinateSmooth)
  rw [contDiff_iff_contDiffAt]
  intro time
  have inputIn : insertion time ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) := by
    refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
    change ‖coordinateDisk (coordinatePoint point time)‖ < family.collarRadius
    rw [coordinateDisk_coordinatePoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have domainOpen : IsOpen
      (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius)) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod
      (coordinateCollar_isOpen family.collarRadius))
  have outer := family.vSmooth.contDiffAt (domainOpen.mem_nhds inputIn)
  simpa [Function.comp_def, insertion, uncurriedCell] using
    outer.comp time insertionSmooth.contDiffAt

theorem v_time_fderiv_periodic
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    Function.Periodic
      (fun time => fderiv ℝ (family.v epsilon parameter.val point) time)
      (2 * Real.pi) := by
  apply fderiv_periodic_of_contDiff
    (smooth := v_time_contDiff cellLength family epsilon epsilonIn parameter
      point pointIn)
  exact family.vPeriodic epsilon epsilonIn parameter.val
    (parameter_mem_open cellLength family parameter) point
    (closed_disk_mem_collar cellLength family point pointIn)

theorem cellDerivative_eq_uncurriedCell_fderiv
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    cellDerivative (family.v epsilon parameter.val) point time =
      fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint point time))
        (cellArgumentTimeCLM 1) := by
  let base : CellArgument :=
    (epsilon, (parameter.val, coordinatePoint point 0))
  let timeSection : ℝ → CellArgument :=
    (fun _ : ℝ => base) + cellArgumentTimeCLM
  have timeSectionDerivative :
      HasFDerivAt timeSection cellArgumentTimeCLM time := by
    simpa only [zero_add] using
      (hasFDerivAt_const (x := time) base).add
        cellArgumentTimeCLM.hasFDerivAt
  have timeSectionValue (current : ℝ) : timeSection current =
      (epsilon, (parameter.val, coordinatePoint point current)) := by
    apply Prod.ext
    · simp [timeSection, base, cellArgumentTimeCLM_apply]
    · apply Prod.ext
      · simp [timeSection, base, cellArgumentTimeCLM_apply]
      · ext coordinate
        fin_cases coordinate <;>
          simp [timeSection, base, cellArgumentTimeCLM_apply, coordinatePoint,
            tangentDirection, basisVector, vector]
  have sectionValue := timeSectionValue time
  have inputIn : timeSection time ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) := by
    rw [sectionValue]
    refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
    change ‖coordinateDisk (coordinatePoint point time)‖ <
      family.collarRadius
    rw [coordinateDisk_coordinatePoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have outerDifferentiable : DifferentiableAt ℝ
      (uncurriedCell family.v) (timeSection time) :=
    (family.vSmooth.contDiffAt
      ((isOpen_Ioo.prod (isOpen_Ioo.prod
        (coordinateCollar_isOpen family.collarRadius))).mem_nhds inputIn))
      |>.differentiableAt (by simp)
  have chain := fderiv_comp (x := time) outerDifferentiable
    timeSectionDerivative.differentiableAt
  rw [timeSectionDerivative.fderiv, sectionValue] at chain
  have compositionIdentity :
      uncurriedCell family.v ∘ timeSection =
        family.v epsilon parameter.val point := by
    funext current
    rw [Function.comp_apply, timeSectionValue current]
    change family.v epsilon parameter.val
      (coordinateDisk (coordinatePoint point current)) current =
        family.v epsilon parameter.val point current
    rw [coordinateDisk_coordinatePoint]
  rw [compositionIdentity] at chain
  have evaluated := congrArg (fun derivative : ℝ →L[ℝ] Vec =>
    derivative 1) chain
  simpa [cellDerivative] using evaluated

theorem exists_v_cellDerivative_bound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (epsilon : ℝ),
        epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero →
        |epsilon| ≤ family.epsilonZero / 2 →
        ∀ (parameter : Set.Icc family.lower family.upper)
          (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
          ‖cellDerivative (family.v epsilon parameter.val) point time‖ ≤
            bound := by
  obtain ⟨rawBound, rawBoundUpper⟩ :=
    exists_jointV_fderiv_norm_bound cellLength family
  let timeDirectionNorm := ‖cellArgumentTimeCLM 1‖
  let bound := max 1 (rawBound * timeDirectionNorm)
  refine ⟨bound, le_max_left _ _, ?_⟩
  intro epsilon epsilonIn epsilonSmall parameter point pointIn time
  change ‖fderiv ℝ (family.v epsilon parameter.val point) time 1‖ ≤ bound
  rw [periodic_eq_fundamentalTime _
    (v_time_fderiv_periodic cellLength family epsilon epsilonIn parameter
      point pointIn) time]
  change ‖cellDerivative (family.v epsilon parameter.val) point
    (fundamentalTime time)‖ ≤ bound
  rw [cellDerivative_eq_uncurriedCell_fderiv cellLength family epsilon
    epsilonIn parameter point pointIn (fundamentalTime time)]
  have compactIn :
      (epsilon,
        (parameter.val, coordinatePoint point (fundamentalTime time))) ∈
        compactCellArguments family := by
    change epsilon ∈ Set.Icc (-family.epsilonZero / 2)
        (family.epsilonZero / 2) ∧
      parameter.val ∈ Set.Icc family.lower family.upper ∧ _
    refine ⟨⟨by linarith [(abs_le.mp epsilonSmall).1],
      by linarith [(abs_le.mp epsilonSmall).2]⟩, parameter.property, ?_⟩
    exact ⟨(point, fundamentalTime time),
      ⟨by simpa [Metric.mem_closedBall, dist_zero_right],
        ⟨(fundamentalTime_mem_Ico time).1,
          (fundamentalTime_mem_Ico time).2.le⟩⟩, rfl⟩
  calc
    ‖fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint point (fundamentalTime time)))
        (cellArgumentTimeCLM 1)‖ ≤
      ‖fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint point (fundamentalTime time)))‖ *
          timeDirectionNorm := by
      simpa [timeDirectionNorm] using
        (ContinuousLinearMap.le_opNorm
          (fderiv ℝ (uncurriedCell family.v)
            (epsilon,
              (parameter.val, coordinatePoint point (fundamentalTime time))))
          (cellArgumentTimeCLM 1))
    _ ≤ rawBound * timeDirectionNorm :=
      mul_le_mul_of_nonneg_right (rawBoundUpper _ compactIn) (norm_nonneg _)
    _ ≤ bound := le_max_right _ _

theorem v_cellDerivative_coordinate_one
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    (cellDerivative (family.v epsilon parameter.val) point time) 1 =
      planeDot (fderiv ℝ (family.tilt epsilon parameter.val) time 1) point +
        (fderiv ℝ (family.remainder epsilon parameter.val point) time 1) 1 := by
  have vSmooth := v_time_contDiff cellLength family epsilon epsilonIn
    parameter point pointIn
  have tiltSmooth := tilt_time_contDiff cellLength family epsilon epsilonIn
    parameter
  have remainderSmooth := remainder_time_contDiff cellLength family epsilon
    epsilonIn parameter point pointIn
  have coordinateIdentity :
      (fun current => (family.v epsilon parameter.val point current) 1) =
      (fun current => planeDot (family.tilt epsilon parameter.val current) point +
        (family.remainder epsilon parameter.val point current) 1) := by
    funext current
    rw [family.normalizedChart epsilon epsilonIn parameter.val
      parameter.property point pointIn current]
    simp [planeEmbedding, tangentDirection, basisVector, vector]
  have vCoordinateDerivative := fderiv_comp (x := time)
    (vecCoordinateCLM 1).differentiableAt
    ((vSmooth.differentiable (by simp)).differentiableAt)
  rw [(vecCoordinateCLM 1).fderiv] at vCoordinateDerivative
  change fderiv ℝ (fun current =>
      (family.v epsilon parameter.val point current) 1) time = _
    at vCoordinateDerivative
  rw [coordinateIdentity] at vCoordinateDerivative
  have dotDerivative := fderiv_comp (x := time)
    (planeDotCLM point).differentiableAt
    ((tiltSmooth.differentiable (by simp)).differentiableAt)
  rw [(planeDotCLM point).fderiv] at dotDerivative
  change fderiv ℝ (fun current =>
      planeDot (family.tilt epsilon parameter.val current) point) time = _
    at dotDerivative
  have remainderCoordinateDerivative := fderiv_comp (x := time)
    (vecCoordinateCLM 1).differentiableAt
    ((remainderSmooth.differentiable (by simp)).differentiableAt)
  rw [(vecCoordinateCLM 1).fderiv] at remainderCoordinateDerivative
  change fderiv ℝ (fun current =>
      (family.remainder epsilon parameter.val point current) 1) time = _
    at remainderCoordinateDerivative
  have sumDerivative := fderiv_add
    ((planeDotCLM point).differentiableAt.comp time
      ((tiltSmooth.differentiable (by simp)).differentiableAt))
    ((vecCoordinateCLM 1).differentiableAt.comp time
      ((remainderSmooth.differentiable (by simp)).differentiableAt))
  change fderiv ℝ (fun current =>
      planeDot (family.tilt epsilon parameter.val current) point +
        (family.remainder epsilon parameter.val point current) 1) time = _
    at sumDerivative
  rw [sumDerivative] at vCoordinateDerivative
  have evaluated := congrArg (fun derivative : ℝ →L[ℝ] ℝ => derivative 1)
    vCoordinateDerivative
  have dotDerivative' :
      fderiv ℝ ((planeDotCLM point) ∘
        family.tilt epsilon parameter.val) time =
        planeDotCLM point ∘SL
          fderiv ℝ (family.tilt epsilon parameter.val) time := by
    have compIdentity :
        (planeDotCLM point) ∘ family.tilt epsilon parameter.val =
          (fun current =>
            planeDot (family.tilt epsilon parameter.val current) point) := by
      funext current
      exact planeDotCLM_apply point _
    rw [compIdentity]
    exact dotDerivative
  have remainderDerivative' :
      fderiv ℝ ((vecCoordinateCLM 1) ∘
        family.remainder epsilon parameter.val point) time =
        vecCoordinateCLM 1 ∘SL
          fderiv ℝ (family.remainder epsilon parameter.val point) time := by
    have compIdentity :
        (vecCoordinateCLM 1) ∘
            family.remainder epsilon parameter.val point =
          (fun current =>
            (family.remainder epsilon parameter.val point current) 1) := by
      funext current
      exact vecCoordinateCLM_apply 1 _
    rw [compIdentity]
    exact remainderCoordinateDerivative
  rw [dotDerivative', remainderDerivative'] at evaluated
  simpa [cellDerivative] using evaluated.symm

theorem abs_v_cellDerivative_coordinate_one_le
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    |(cellDerivative (family.v epsilon parameter.val) point time) 1| ≤
      2 * (family.bound * |epsilon|) := by
  rw [v_cellDerivative_coordinate_one cellLength family epsilon epsilonIn
    parameter point pointIn time]
  calc
    |planeDot (fderiv ℝ (family.tilt epsilon parameter.val) time 1) point +
        (fderiv ℝ (family.remainder epsilon parameter.val point) time 1) 1| ≤
      |planeDot (fderiv ℝ (family.tilt epsilon parameter.val) time 1) point| +
        |(fderiv ℝ (family.remainder epsilon parameter.val point) time 1) 1| :=
      abs_add_le _ _
    _ ≤ ‖fderiv ℝ (family.tilt epsilon parameter.val) time 1‖ * ‖point‖ +
        ‖fderiv ℝ (family.remainder epsilon parameter.val point) time 1‖ :=
      add_le_add (abs_planeDot_le_norm_mul_norm _ _)
        (coordinate_abs_le_norm _ 1)
    _ ≤ (family.bound * |epsilon|) * 1 +
        (family.bound * |epsilon|) * 1 := by
      apply add_le_add
      · have tiltBound :=
          tilt_time_fderiv_apply_norm_le_physicalBound_allTime
            cellLength family epsilon epsilonIn parameter time 1
        simp only [norm_one, mul_one] at tiltBound
        exact mul_le_mul tiltBound pointIn (norm_nonneg _)
          (mul_nonneg
            (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _))
      · simpa only [norm_one, mul_one] using
          (remainder_time_fderiv_apply_norm_le_physicalBound_allTime
            cellLength family epsilon epsilonIn parameter point pointIn time 1)
    _ = 2 * (family.bound * |epsilon|) := by ring

private def fullPlaneMatrixAction (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (point : Plane) : Plane :=
  WithLp.toLp 2 (matrix *ᵥ fun coordinate => point coordinate)

private theorem fullPlaneMatrixAction_mul
    (first second : Matrix (Fin 2) (Fin 2) ℝ) (point : Plane) :
    fullPlaneMatrixAction (first * second) point =
      fullPlaneMatrixAction first (fullPlaneMatrixAction second point) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [fullPlaneMatrixAction, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

private theorem fullPlanarRotation_norm_sq (angle : ℝ) (point : Plane) :
    ‖fullPlaneMatrixAction (Grad.GeometryClosure.planarRotation angle) point‖ ^ 2 =
      ‖point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [fullPlaneMatrixAction, Grad.GeometryClosure.planarRotation,
    dotProduct, Fin.sum_univ_two]
  nlinarith [Real.sin_sq_add_cos_sq angle]

private theorem fullDiagonal_upper_norm_sq
    (rho : ℝ) (point : Plane) (rhoNonnegative : 0 ≤ rho)
    (rhoUpper : rho < 1) :
    ‖fullPlaneMatrixAction
        !![Real.sqrt (1 + rho), 0; 0, Real.sqrt (1 - rho)] point‖ ^ 2 ≤
      (1 + rho) * ‖point‖ ^ 2 := by
  have plusNonnegative : 0 ≤ 1 + rho := by linarith
  have minusNonnegative : 0 ≤ 1 - rho := by linarith
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [fullPlaneMatrixAction, dotProduct, Fin.sum_univ_two]
  rw [mul_pow, mul_pow]
  rw [Real.sq_sqrt plusNonnegative, Real.sq_sqrt minusNonnegative]
  nlinarith [sq_nonneg (point 1)]

theorem seedAction_norm_sq_le
    (rho alpha delta parameter time : ℝ) (point : Plane)
    (rhoNonnegative : 0 ≤ rho) (rhoUpper : rho < 1) :
    ‖seedAction rho alpha delta parameter time point‖ ^ 2 ≤
      (1 + rho) * ‖point‖ ^ 2 := by
  let angle := Grad.GeometryClosure.seedAngle alpha delta parameter time
  let rotatedPoint := fullPlaneMatrixAction
    (Grad.GeometryClosure.planarRotation (-angle)) point
  have seedIdentity :
      seedAction rho alpha delta parameter time point =
        fullPlaneMatrixAction (Grad.GeometryClosure.planarRotation angle)
          (fullPlaneMatrixAction
            !![Real.sqrt (1 + rho), 0; 0, Real.sqrt (1 - rho)]
            rotatedPoint) := by
    change fullPlaneMatrixAction
      (Grad.GeometryClosure.harmonicSeedMatrix rho alpha delta parameter time)
        point = _
    rw [Grad.GeometryClosure.harmonicSeedMatrix_formula]
    rw [fullPlaneMatrixAction_mul, fullPlaneMatrixAction_mul]
  rw [seedIdentity, fullPlanarRotation_norm_sq]
  calc
    _ ≤ (1 + rho) * ‖rotatedPoint‖ ^ 2 :=
      fullDiagonal_upper_norm_sq rho rotatedPoint rhoNonnegative rhoUpper
    _ = (1 + rho) * ‖point‖ ^ 2 := by
      rw [fullPlanarRotation_norm_sq]

theorem seedAction_norm_le_two
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (parameter time : ℝ) (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    ‖seedAction family.rho family.alpha family.delta parameter time point‖ < 2 := by
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
  have seedUpper := seedAction_norm_sq_le family.rho family.alpha family.delta
    parameter time point family.rhoPositive.le
    (by linarith [family.rhoSmall] : family.rho < 1)
  nlinarith [sq_le_sq₀ (norm_nonneg point) zero_le_one |>.mpr pointIn,
    family.rhoSmall]

theorem v_norm_le_four
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (errorSmall : family.bound * |epsilon| ≤ 1) :
    ‖family.v epsilon parameter.val point time‖ ≤ 4 := by
  rw [family.normalizedChart epsilon epsilonIn parameter.val
    parameter.property point pointIn time]
  have factorNonnegative := normalizedFactor_nonnegative
    (family.tilt epsilon parameter.val time)
  have factorLe := normalizedFactor_le_one
    (family.tilt epsilon parameter.val time)
    (family.tiltBound epsilon epsilonIn parameter.val parameter.property time)
  have seedBound := (seedAction_norm_le_two cellLength family parameter.val
    time point pointIn).le
  have tiltBound := tilt_value_norm_le_physicalBound_allTime cellLength family
    epsilon epsilonIn parameter time
  have remainderBound := remainder_value_norm_le_physicalBound_allTime
    cellLength family epsilon epsilonIn parameter point pointIn time
  calc
    ‖normalizedFactor (family.tilt epsilon parameter.val time) •
          planeEmbedding
            (seedAction family.rho family.alpha family.delta parameter.val
              time point) +
        planeDot (family.tilt epsilon parameter.val time) point •
          tangentDirection +
        family.remainder epsilon parameter.val point time‖ ≤
      ‖normalizedFactor (family.tilt epsilon parameter.val time) •
          planeEmbedding
            (seedAction family.rho family.alpha family.delta parameter.val
              time point)‖ +
        ‖planeDot (family.tilt epsilon parameter.val time) point •
          tangentDirection‖ +
        ‖family.remainder epsilon parameter.val point time‖ := by
      calc
        _ ≤ ‖normalizedFactor (family.tilt epsilon parameter.val time) •
              planeEmbedding
                (seedAction family.rho family.alpha family.delta parameter.val
                  time point) +
            planeDot (family.tilt epsilon parameter.val time) point •
              tangentDirection‖ +
            ‖family.remainder epsilon parameter.val point time‖ :=
          norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ 2 + (family.bound * |epsilon|) +
        (family.bound * |epsilon|) := by
      apply add_le_add
      · apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg factorNonnegative, planeEmbedding_norm]
          exact (mul_le_mul factorLe seedBound (norm_nonneg _) zero_le_one).trans
            (by nlinarith)
        · rw [norm_smul, Real.norm_eq_abs]
          have tangentNorm : ‖tangentDirection‖ = 1 := by
            apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
            rw [EuclideanSpace.real_norm_sq_eq]
            simp [tangentDirection, basisVector]
          rw [tangentNorm, mul_one]
          exact (abs_planeDot_le_norm_mul_norm _ _).trans
            ((mul_le_mul tiltBound pointIn (norm_nonneg _) (by
              exact mul_nonneg
                (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _))).trans
              (by simp))
      · exact remainderBound
    _ ≤ 4 := by linarith

theorem tangentGenerator_norm_le (point : Vec) :
    ‖tangentGenerator point‖ ≤ ‖point‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [tangentGenerator, vector, Fin.sum_univ_three]
  nlinarith [sq_nonneg (point 2)]

theorem tangentDirection_norm : ‖tangentDirection‖ = 1 :=
  basisVector_one_norm

theorem exists_affineStateDerivative_bound
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (epsilon : ℝ),
        epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero →
        |epsilon| ≤ family.epsilonZero / 2 →
        |epsilon| ≤ 1 → family.bound * |epsilon| ≤ 1 →
        ∀ (parameter : Set.Icc family.lower family.upper)
          (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
          ‖affineStateDerivative cellLength epsilon
            (family.v epsilon parameter.val) point time‖ ≤ bound := by
  obtain ⟨cellBound, cellBoundAtLeastOne, cellBoundUpper⟩ :=
    exists_v_cellDerivative_bound cellLength family
  let bound := cellBound + 4 + cellLength
  have boundAtLeastOne : 1 ≤ bound := by
    dsimp [bound]
    linarith
  refine ⟨bound, boundAtLeastOne, ?_⟩
  intro epsilon epsilonIn epsilonDomain epsilonUnit errorSmall parameter point
    pointIn time
  have vBound := v_norm_le_four cellLength family epsilon epsilonIn parameter
    point pointIn time errorSmall
  have cellUpper := cellBoundUpper epsilon epsilonIn epsilonDomain parameter
    point pointIn time
  calc
    ‖affineStateDerivative cellLength epsilon
        (family.v epsilon parameter.val) point time‖ ≤
      ‖cellDerivative (family.v epsilon parameter.val) point time‖ +
        ‖epsilon • tangentGenerator
          (family.v epsilon parameter.val point time)‖ +
        ‖cellLength • tangentDirection‖ := by
      unfold affineStateDerivative
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ cellBound + |epsilon| * 4 + cellLength * 1 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos cellLengthPositive,
        tangentDirection_norm]
      exact add_le_add (add_le_add cellUpper
        (mul_le_mul_of_nonneg_left
          (tangentGenerator_norm_le _ |>.trans vBound) (abs_nonneg _)))
        (le_refl _)
    _ ≤ bound := by
      dsimp [bound]
      nlinarith

theorem abs_affineStateDerivative_coordinate_one_sub_cellLength_le
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (errorSmall : family.bound * |epsilon| ≤ 1) :
    |(affineStateDerivative cellLength epsilon
        (family.v epsilon parameter.val) point time) 1 - cellLength| ≤
      6 * (family.bound * |epsilon|) := by
  have coordinateIdentity :
      (affineStateDerivative cellLength epsilon
        (family.v epsilon parameter.val) point time) 1 - cellLength =
      (cellDerivative (family.v epsilon parameter.val) point time) 1 +
        epsilon * (family.v epsilon parameter.val point time) 0 := by
    simp [affineStateDerivative, tangentGenerator, tangentDirection,
      basisVector, vector, smul_eq_mul]
  rw [coordinateIdentity]
  calc
    |(cellDerivative (family.v epsilon parameter.val) point time) 1 +
        epsilon * (family.v epsilon parameter.val point time) 0| ≤
      |(cellDerivative (family.v epsilon parameter.val) point time) 1| +
        |epsilon * (family.v epsilon parameter.val point time) 0| :=
      abs_add_le _ _
    _ ≤ 2 * (family.bound * |epsilon|) +
        |epsilon| * ‖family.v epsilon parameter.val point time‖ := by
      apply add_le_add
      · exact abs_v_cellDerivative_coordinate_one_le cellLength family epsilon
          epsilonIn parameter point pointIn time
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (coordinate_abs_le_norm _ 0) (abs_nonneg epsilon)
    _ ≤ 2 * (family.bound * |epsilon|) +
        (family.bound * |epsilon|) * 4 := by
      apply add_le_add (le_refl (2 * (family.bound * |epsilon|)))
      exact mul_le_mul
        (by simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right family.boundAtLeastOne
            (abs_nonneg epsilon)))
        (v_norm_le_four cellLength family epsilon epsilonIn parameter point
          pointIn time errorSmall)
        (norm_nonneg _) (mul_nonneg
          (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _))
    _ = 6 * (family.bound * |epsilon|) := by ring

/-- Quantitative transversality of the two disk columns and the affine cell
time column.  This is the algebraic core of the all-point sampled immersion. -/
theorem cell_full_columns_injective_of_bounds
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (period : ℕ) (periodPositive : 0 < period)
    (diskDerivative : Plane →L[ℝ] Vec) (timeColumn : Vec)
    (error bound : ℝ) (errorNonnegative : 0 ≤ error)
    (boundAtLeastOne : 1 ≤ bound)
    (errorSmall : error < min (1 / 16) (cellLength / (64 * bound)))
    (diskLower : ∀ direction : Plane,
      (1 / 8 : ℝ) * ‖direction‖ ≤ ‖diskDerivative direction‖)
    (diskCoordinateUpper : ∀ direction : Plane,
      |(diskDerivative direction) 1| ≤ 2 * error * ‖direction‖)
    (timeColumnUpper : ‖timeColumn‖ ≤ bound)
    (timeCoordinateClose : |timeColumn 1 - cellLength| ≤ 6 * error) :
    Function.Injective (fun argument : Plane × ℝ =>
      diskDerivative argument.1 +
        (((period : ℝ) * argument.2) • timeColumn)) := by
  intro first second equality
  let diskDifference := first.1 - second.1
  let timeDifference := first.2 - second.2
  let scaledTime := (period : ℝ) * timeDifference
  have totalZero : diskDerivative diskDifference +
      scaledTime • timeColumn = 0 := by
    dsimp [diskDifference, timeDifference, scaledTime]
    rw [map_sub]
    calc
      diskDerivative first.1 - diskDerivative second.1 +
          ((period : ℝ) * (first.2 - second.2)) • timeColumn =
        (diskDerivative first.1 +
            ((period : ℝ) * first.2) • timeColumn) -
          (diskDerivative second.1 +
            ((period : ℝ) * second.2) • timeColumn) := by
              module
      _ = 0 := sub_eq_zero.mpr equality
  have diskEquality : diskDerivative diskDifference =
      -(scaledTime • timeColumn) := eq_neg_of_add_eq_zero_left totalZero
  have normUpper : ‖diskDerivative diskDifference‖ ≤
      |scaledTime| * bound := by
    rw [diskEquality, norm_neg, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left timeColumnUpper (abs_nonneg _)
  have coordinateEquality : (diskDerivative diskDifference) 1 =
      -(scaledTime * timeColumn 1) := by
    have evaluated := congrArg (fun value : Vec => value 1) diskEquality
    simpa [smul_eq_mul] using evaluated
  have timeCoordinateLower : cellLength - 6 * error ≤ timeColumn 1 := by
    have := (abs_le.mp timeCoordinateClose).1
    linarith
  have errorCell : error < cellLength / (64 * bound) :=
    lt_of_lt_of_le errorSmall (min_le_right _ _)
  have boundPositive : 0 < bound := lt_of_lt_of_le zero_lt_one boundAtLeastOne
  have denominatorPositive : 0 < 64 * bound := mul_pos (by norm_num) boundPositive
  have errorTimesBound : error * bound < cellLength / 64 := by
    have multiplied := (lt_div_iff₀ denominatorPositive).mp errorCell
    nlinarith
  have timeCoordinateHalf : cellLength / 2 ≤ timeColumn 1 := by
    have : 6 * error < cellLength / 2 := by
      nlinarith [boundAtLeastOne]
    linarith
  have timeCoordinatePositive : 0 < timeColumn 1 :=
    lt_of_lt_of_le (half_pos cellLengthPositive) timeCoordinateHalf
  have coordinateMagnitudeLower : cellLength / 2 ≤ |timeColumn 1| := by
    rw [abs_of_pos timeCoordinatePositive]
    exact timeCoordinateHalf
  have scaledCoordinateUpper :
      |scaledTime| * (cellLength / 2) ≤
        2 * error * ‖diskDifference‖ := by
    calc
      |scaledTime| * (cellLength / 2) ≤
          |scaledTime| * |timeColumn 1| :=
        mul_le_mul_of_nonneg_left coordinateMagnitudeLower (abs_nonneg _)
      _ = |(diskDerivative diskDifference) 1| := by
        rw [coordinateEquality, abs_neg]
        simp [scaledTime, abs_mul, mul_assoc]
      _ ≤ _ := diskCoordinateUpper diskDifference
  have diskDifferenceZero : diskDifference = 0 := by
    by_contra diskNonzero
    have diskNormPositive : 0 < ‖diskDifference‖ := norm_pos_iff.mpr diskNonzero
    have lower := diskLower diskDifference
    have firstChain :
        cellLength * ((1 / 8 : ℝ) * ‖diskDifference‖) ≤
          cellLength * (|scaledTime| * bound) :=
      mul_le_mul_of_nonneg_left (lower.trans normUpper) cellLengthPositive.le
    have secondChain :
        (2 * bound) * (|scaledTime| * (cellLength / 2)) ≤
          (2 * bound) * (2 * error * ‖diskDifference‖) :=
      mul_le_mul_of_nonneg_left scaledCoordinateUpper
        (mul_nonneg (by norm_num) boundPositive.le)
    have combined :
        cellLength * ((1 / 8 : ℝ) * ‖diskDifference‖) ≤
          4 * error * bound * ‖diskDifference‖ := by
      calc
        cellLength * ((1 / 8 : ℝ) * ‖diskDifference‖) ≤
            cellLength * (|scaledTime| * bound) := firstChain
        _ = (2 * bound) * (|scaledTime| * (cellLength / 2)) := by ring
        _ ≤ (2 * bound) * (2 * error * ‖diskDifference‖) :=
          secondChain
        _ = 4 * error * bound * ‖diskDifference‖ := by ring
    have strictCoefficient : 4 * error * bound < cellLength / 8 := by
      nlinarith
    have strictScaled := mul_lt_mul_of_pos_right strictCoefficient
      diskNormPositive
    nlinarith
  have scaledTimeZero : scaledTime = 0 := by
    rw [diskDifferenceZero, map_zero, zero_add] at totalZero
    have coordinateZero := congrArg (fun value : Vec => value 1) totalZero
    change scaledTime * timeColumn 1 = 0 at coordinateZero
    exact (mul_eq_zero.mp coordinateZero).resolve_right
      timeCoordinatePositive.ne'
  have timeDifferenceZero : timeDifference = 0 := by
    dsimp [scaledTime] at scaledTimeZero
    exact (mul_eq_zero.mp scaledTimeZero).resolve_left
      (Nat.cast_pos.mpr periodPositive).ne'
  apply Prod.ext
  · exact sub_eq_zero.mp diskDifferenceZero
  · exact sub_eq_zero.mp timeDifferenceZero

theorem sampledPositionCoordinateValue_differentiableAt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    DifferentiableAt ℝ
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (coordinateDirection point time) := by
  let argument : ℝ × Vec :=
    (parameter.val, coordinateDirection point time)
  have planarIdentity : planarPart (coordinateDirection point time) = point := by
    ext coordinate
    fin_cases coordinate <;>
      simp [planarPart, coordinateDirection, vector]
  have argumentIn : argument ∈ sampledPhysicalCollar cellLength family := by
    refine ⟨parameter_mem_open cellLength family parameter, ?_⟩
    change planarPart (coordinateDirection point time) ∈
      Metric.ball 0 family.collarRadius
    rw [Metric.mem_ball, dist_zero_right, planarIdentity]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have jointDifferentiable : DifferentiableAt ℝ
      (sampledPositionJointLift cellLength family period) argument :=
    ((sampledPositionJointLift_contDiffOn cellLength family period epsilonIn)
      |>.contDiffAt
        ((sampledPhysicalCollar_isOpen cellLength family).mem_nhds argumentIn))
      |>.differentiableAt (by simp)
  have insertionDifferentiable : DifferentiableAt ℝ
      (fun value : Vec => (parameter.val, value))
      (coordinateDirection point time) := by fun_prop
  have composed := jointDifferentiable.comp
    (coordinateDirection point time) insertionDifferentiable
  change DifferentiableAt ℝ
    (fun value : Vec =>
      sampledPositionJointLift cellLength family period (parameter.val, value))
    (coordinateDirection point time)
  simpa [Function.comp_def, argument] using composed

theorem sampledPositionCoordinateValue_fderiv_disk_allPoints
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (direction : Plane) :
    fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter.val)
        (coordinateDirection point time) (coordinateDirection direction 0) =
      rotation time
        (fderiv ℝ (fun argument : Plane =>
          family.v (sampledEpsilon period) parameter.val argument
            ((period : ℝ) * time)) point direction) := by
  let diskInsertion : Plane → Vec := fun argument =>
    coordinateDirection argument time
  have insertionHasDerivative : HasFDerivAt diskInsertion physicalDiskCLM
      point := by
    let base : Vec := coordinateDirection 0 time
    have functionIdentity : diskInsertion =
        (fun _ : Plane => base) + physicalDiskCLM := by
      funext argument
      ext coordinate
      fin_cases coordinate <;>
        simp [diskInsertion, base, physicalDiskCLM_apply, coordinateDirection,
          vector]
    rw [functionIdentity]
    simpa only [zero_add] using
      (hasFDerivAt_const (x := point) base).add physicalDiskCLM.hasFDerivAt
  have insertionValue : diskInsertion point = coordinateDirection point time :=
    rfl
  have chartDifferentiable : DifferentiableAt ℝ
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (diskInsertion point) := by
    rw [insertionValue]
    exact sampledPositionCoordinateValue_differentiableAt cellLength family
      period epsilonIn parameter point pointIn time
  have chartChain := fderiv_comp (x := point) chartDifferentiable
    insertionHasDerivative.differentiableAt
  rw [insertionHasDerivative.fderiv, insertionValue] at chartChain
  let cellTime := (period : ℝ) * time
  let cellMap : Plane → Vec := fun argument =>
    family.v (sampledEpsilon period) parameter.val argument cellTime
  have cellDifferentiable : DifferentiableAt ℝ cellMap point := by
    let diskSection : Plane → CellArgument := fun argument =>
      (sampledEpsilon period,
        (parameter.val, coordinatePoint argument cellTime))
    have inputIn : diskSection point ∈
        Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
          (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
            coordinateCollar family.collarRadius) := by
      refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
      change ‖coordinateDisk (coordinatePoint point cellTime)‖ <
        family.collarRadius
      rw [coordinateDisk_coordinatePoint]
      exact lt_of_le_of_lt pointIn family.collarLarge
    have outer := family.vSmooth.contDiffAt
      ((isOpen_Ioo.prod (isOpen_Ioo.prod
        (coordinateCollar_isOpen family.collarRadius))).mem_nhds inputIn)
      |>.differentiableAt (by simp)
    have sectionDifferentiable : DifferentiableAt ℝ diskSection point := by
      have coordinateSmooth : ContDiff ℝ ∞
          (fun argument : Plane => coordinatePoint argument cellTime) :=
        coordinatePoint_uncurried_contDiff.comp
          (contDiff_id.prodMk contDiff_const)
      exact ((contDiff_const.prodMk
        (contDiff_const.prodMk coordinateSmooth)).differentiable (by simp))
        |>.differentiableAt
    simpa [cellMap, diskSection, Function.comp_def, uncurriedCell] using
      outer.comp point sectionDifferentiable
  let radiusBase : Vec := ((period : ℝ) * cellLength) • basisVector 0
  let rotationInput : Plane → Vec :=
    (fun _ : Plane => radiusBase) + cellMap
  have rotationInputDifferentiable : DifferentiableAt ℝ rotationInput point :=
    (differentiableAt_const radiusBase).add cellDifferentiable
  have rotationInputDerivative : fderiv ℝ rotationInput point =
      fderiv ℝ cellMap point := by
    rw [fderiv_add (differentiableAt_const radiusBase) cellDifferentiable,
      (hasFDerivAt_const (x := point) radiusBase).fderiv, zero_add]
  have rotatedDerivative :
      fderiv ℝ (rotationCLM time ∘ rotationInput) point =
        rotationCLM time ∘L fderiv ℝ cellMap point := by
    rw [fderiv_comp (x := point) (rotationCLM time).differentiableAt
      rotationInputDifferentiable, (rotationCLM time).fderiv,
      rotationInputDerivative]
  have compositionIdentity :
      sampledPositionCoordinateValue cellLength family period parameter.val ∘
          diskInsertion = rotationCLM time ∘ rotationInput := by
    funext argument
    change sampledPositionJointLift cellLength family period
        (parameter.val, diskInsertion argument) =
      rotation time (rotationInput argument)
    rw [sampledPositionJointLift_eq]
    have planarIdentity : planarPart (diskInsertion argument) = argument := by
      ext coordinate
      fin_cases coordinate <;>
        simp [diskInsertion, planarPart, coordinateDirection, vector]
    have timeIdentity : (diskInsertion argument) 2 = time := by
      simp [diskInsertion, coordinateDirection, vector]
    rw [planarIdentity, timeIdentity]
    rfl
  rw [compositionIdentity, rotatedDerivative] at chartChain
  have evaluated := congrArg (fun derivative : Plane →L[ℝ] Vec =>
    derivative direction) chartChain
  simpa [cellMap] using evaluated.symm

theorem rotation_path_hasDerivAt
    (path : ℝ → Vec) (time : ℝ) (pathDerivative : Vec)
    (pathHasDerivative : HasDerivAt path pathDerivative time) :
    HasDerivAt (fun current => rotation current (path current))
      (rotation time (tangentGenerator (path time) + pathDerivative)) time := by
  have coordinateDerivative (coordinate : Fin 3) :
      HasDerivAt (fun current => path current coordinate)
        (pathDerivative coordinate) time := by
    have evaluated :=
      (hasDerivAt_const (x := time) (vecCoordinateCLM coordinate)).clm_apply
        pathHasDerivative
    simp at evaluated
    exact evaluated
  let coordinateEquiv :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have piDerivative : HasDerivAt
      (fun current coordinate => rotation current (path current) coordinate)
      (fun coordinate =>
        rotation time (tangentGenerator (path time) + pathDerivative)
          coordinate) time := by
    apply hasDerivAt_iff_hasFDerivAt.mpr
    let componentDerivative : Fin 3 → (ℝ →L[ℝ] ℝ) := fun coordinate =>
      ContinuousLinearMap.toSpanSingleton ℝ
        (rotation time (tangentGenerator (path time) + pathDerivative)
          coordinate)
    have derivativeIdentity :
        ContinuousLinearMap.toSpanSingleton ℝ
            (fun coordinate =>
              rotation time (tangentGenerator (path time) + pathDerivative)
                coordinate) =
          ContinuousLinearMap.pi componentDerivative := by
      apply ContinuousLinearMap.ext
      intro scalar
      funext coordinate
      simp [componentDerivative]
    rw [derivativeIdentity, hasFDerivAt_pi]
    intro coordinate
    fin_cases coordinate
    · have derivative := ((hasDerivAt_id (x := time)).cos.smul
          (coordinateDerivative 0)).sub
        ((hasDerivAt_id (x := time)).sin.smul (coordinateDerivative 1))
      have derivativeValue :
          Real.cos time * pathDerivative 0 +
              -(Real.sin time * path time 0) -
            (Real.sin time * pathDerivative 1 +
              Real.cos time * path time 1) =
            rotation time (tangentGenerator (path time) + pathDerivative) 0 := by
        simp [rotation, tangentGenerator, vector]
        ring
      have rawValue :
          Real.cos (id time) • pathDerivative 0 +
              (-Real.sin (id time) * 1) • path time 0 -
            (Real.sin (id time) • pathDerivative 1 +
              (Real.cos (id time) * 1) • path time 1) =
          Real.cos time * pathDerivative 0 +
              -(Real.sin time * path time 0) -
            (Real.sin time * pathDerivative 1 +
              Real.cos time * path time 1) := by
        simp [smul_eq_mul]
      rw [rawValue] at derivative
      have derivative' : HasDerivAt
        (fun current => Real.cos current * path current 0 -
          Real.sin current * path current 1)
        (Real.cos time * pathDerivative 0 +
            -(Real.sin time * path time 0) -
          (Real.sin time * pathDerivative 1 +
            Real.cos time * path time 1)) time := by
        apply derivative.congr_of_eventuallyEq
        filter_upwards [] with current
        simp [smul_eq_mul]
      rw [derivativeValue] at derivative'
      change HasFDerivAt
        (fun current => Real.cos current * path current 0 -
          Real.sin current * path current 1)
        (ContinuousLinearMap.toSpanSingleton ℝ
          (rotation time (tangentGenerator (path time) + pathDerivative) 0))
        time
      exact derivative'.hasFDerivAt
    · have derivative := ((hasDerivAt_id (x := time)).sin.smul
          (coordinateDerivative 0)).add
        ((hasDerivAt_id (x := time)).cos.smul (coordinateDerivative 1))
      have derivativeValue :
          Real.sin time * pathDerivative 0 +
              Real.cos time * path time 0 +
            (Real.cos time * pathDerivative 1 +
              -(Real.sin time * path time 1)) =
            rotation time (tangentGenerator (path time) + pathDerivative) 1 := by
        simp [rotation, tangentGenerator, vector]
        ring
      have rawValue :
          Real.sin (id time) • pathDerivative 0 +
              (Real.cos (id time) * 1) • path time 0 +
            (Real.cos (id time) • pathDerivative 1 +
              (-Real.sin (id time) * 1) • path time 1) =
          Real.sin time * pathDerivative 0 +
              Real.cos time * path time 0 +
            (Real.cos time * pathDerivative 1 +
              -(Real.sin time * path time 1)) := by
        simp [smul_eq_mul]
      rw [rawValue] at derivative
      have derivative' : HasDerivAt
        (fun current => Real.sin current * path current 0 +
          Real.cos current * path current 1)
        (Real.sin time * pathDerivative 0 +
            Real.cos time * path time 0 +
          (Real.cos time * pathDerivative 1 +
            -(Real.sin time * path time 1))) time := by
        apply derivative.congr_of_eventuallyEq
        filter_upwards [] with current
        simp [smul_eq_mul]
      rw [derivativeValue] at derivative'
      change HasFDerivAt
        (fun current => Real.sin current * path current 0 +
          Real.cos current * path current 1)
        (ContinuousLinearMap.toSpanSingleton ℝ
          (rotation time (tangentGenerator (path time) + pathDerivative) 1))
        time
      exact derivative'.hasFDerivAt
    · simpa [componentDerivative, rotation, tangentGenerator, vector] using
        (coordinateDerivative 2).hasFDerivAt
  have returned :=
    (hasDerivAt_const (x := time) coordinateEquiv.symm.toContinuousLinearMap)
      |>.clm_apply piDerivative
  simpa [coordinateEquiv] using returned

theorem sampledPosition_time_hasDerivAt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    HasDerivAt
      (sampledPositionLift cellLength family period parameter.val point)
      (rotation time (((period : ℝ) •
        affineStateDerivative cellLength (sampledEpsilon period)
          (family.v (sampledEpsilon period) parameter.val) point
          ((period : ℝ) * time)))) time := by
  let epsilon := sampledEpsilon period
  let cellTime := (period : ℝ) * time
  let vSlice := family.v epsilon parameter.val point
  let vDerivative := cellDerivative (family.v epsilon parameter.val) point
    cellTime
  have vDifferentiable : DifferentiableAt ℝ vSlice cellTime :=
    ((v_time_contDiff cellLength family epsilon epsilonIn parameter point
      pointIn).differentiable (by simp)).differentiableAt
  have vRawDerivative := vDifferentiable.hasDerivAt
  have vDerivativeIdentity : vDerivative = deriv vSlice cellTime := by
    change fderiv ℝ vSlice cellTime 1 = deriv vSlice cellTime
    simp
  rw [← vDerivativeIdentity] at vRawDerivative
  have scaleDerivative : HasDerivAt
      (fun current : ℝ => (period : ℝ) * current) (period : ℝ) time := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (x := time)).const_mul (period : ℝ)
  have scaledChain := vRawDerivative.hasFDerivAt.comp time
    scaleDerivative.hasFDerivAt
  have scaledDerivative : HasDerivAt
      (fun current : ℝ => vSlice ((period : ℝ) * current))
      ((period : ℝ) • vDerivative) time := by
    have chainAsDerivative := scaledChain.hasDerivAt
    have derivativeIdentity :
        (ContinuousLinearMap.toSpanSingleton ℝ vDerivative ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (period : ℝ)) 1 =
            (period : ℝ) • vDerivative := by
      ext coordinate
      simp [smul_eq_mul]
    rw [derivativeIdentity] at chainAsDerivative
    apply chainAsDerivative.congr_of_eventuallyEq
    filter_upwards [] with current
    rfl
  let radiusBase : Vec := ((period : ℝ) * cellLength) • basisVector 0
  let rotationPath : ℝ → Vec := fun current =>
    radiusBase + vSlice ((period : ℝ) * current)
  have rotationPathDerivative : HasDerivAt rotationPath
      ((period : ℝ) • vDerivative) time := by
    have raw := (hasDerivAt_const (x := time) radiusBase).add scaledDerivative
    simp only [zero_add] at raw
    apply raw.congr_of_eventuallyEq
    filter_upwards [] with current
    rfl
  have rotated := rotation_path_hasDerivAt rotationPath time
    ((period : ℝ) • vDerivative) rotationPathDerivative
  have periodEpsilon : (period : ℝ) * epsilon = 1 := by
    dsimp [epsilon, sampledEpsilon]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr periodPositive.ne')
  have columnIdentity :
      tangentGenerator (rotationPath time) +
          (period : ℝ) • vDerivative =
        (period : ℝ) •
          affineStateDerivative cellLength epsilon
            (family.v epsilon parameter.val) point cellTime := by
    dsimp [cellTime, vDerivative]
    ext coordinate
    fin_cases coordinate
    · simp [rotationPath, radiusBase, vSlice, affineStateDerivative,
        tangentGenerator, tangentDirection, basisVector, vector, smul_eq_mul]
      rw [← mul_assoc, periodEpsilon, one_mul]
      ring
    · simp [rotationPath, radiusBase, vSlice, affineStateDerivative,
        tangentGenerator, tangentDirection, basisVector, vector, smul_eq_mul]
      rw [← mul_assoc, periodEpsilon, one_mul]
      ring
    · simp [rotationPath, radiusBase, vSlice, affineStateDerivative,
        tangentGenerator, tangentDirection, basisVector, vector, smul_eq_mul]
  rw [columnIdentity] at rotated
  have functionIdentity :
      (fun current => rotation current (rotationPath current)) =
        sampledPositionLift cellLength family period parameter.val point := by
    funext current
    rfl
  rw [functionIdentity] at rotated
  exact rotated

theorem sampledPositionCoordinateValue_fderiv_toroidal_allPoints
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time toroidal : ℝ) :
    fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter.val)
        (coordinateDirection point time) (coordinateDirection 0 toroidal) =
      rotation time (((period : ℝ) * toroidal) •
        affineStateDerivative cellLength (sampledEpsilon period)
          (family.v (sampledEpsilon period) parameter.val) point
          ((period : ℝ) * time)) := by
  let toroidalInsertion : ℝ → Vec := fun current =>
    coordinateDirection point current
  have insertionHasDerivative :
      HasFDerivAt toroidalInsertion physicalToroidalCLM time := by
    let base : Vec := coordinateDirection point 0
    have functionIdentity : toroidalInsertion =
        (fun _ : ℝ => base) + physicalToroidalCLM := by
      funext current
      ext coordinate
      fin_cases coordinate <;>
        simp [toroidalInsertion, base, physicalToroidalCLM_apply,
          coordinateDirection, vector]
    rw [functionIdentity]
    simpa only [zero_add] using
      (hasFDerivAt_const (x := time) base).add
        physicalToroidalCLM.hasFDerivAt
  have chartDifferentiable : DifferentiableAt ℝ
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (toroidalInsertion time) := by
    change DifferentiableAt ℝ
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (coordinateDirection point time)
    exact sampledPositionCoordinateValue_differentiableAt cellLength family
      period epsilonIn parameter point pointIn time
  have chartChain := fderiv_comp (x := time) chartDifferentiable
    insertionHasDerivative.differentiableAt
  rw [insertionHasDerivative.fderiv] at chartChain
  have compositionIdentity :
      sampledPositionCoordinateValue cellLength family period parameter.val ∘
          toroidalInsertion =
        sampledPositionLift cellLength family period parameter.val point := by
    funext current
    change sampledPositionJointLift cellLength family period
        (parameter.val, toroidalInsertion current) = _
    rw [sampledPositionJointLift_eq]
    have planarIdentity : planarPart (toroidalInsertion current) = point := by
      ext coordinate
      fin_cases coordinate <;>
        simp [toroidalInsertion, planarPart, coordinateDirection, vector]
    have timeIdentity : (toroidalInsertion current) 2 = current := by
      simp [toroidalInsertion, coordinateDirection, vector]
    rw [planarIdentity, timeIdentity]
  rw [compositionIdentity,
    (sampledPosition_time_hasDerivAt cellLength family period periodPositive
      epsilonIn parameter point pointIn time).hasFDerivAt.fderiv] at chartChain
  have evaluated := congrArg (fun derivative : ℝ →L[ℝ] Vec =>
    derivative toroidal) chartChain
  have insertionValue : toroidalInsertion time =
      coordinateDirection point time := rfl
  rw [insertionValue] at evaluated
  calc
    _ = toroidal • rotation time ((period : ℝ) •
        affineStateDerivative cellLength (sampledEpsilon period)
          (family.v (sampledEpsilon period) parameter.val) point
          ((period : ℝ) * time)) := by
      simpa using evaluated.symm
    _ = rotation time (((period : ℝ) * toroidal) •
        affineStateDerivative cellLength (sampledEpsilon period)
          (family.v (sampledEpsilon period) parameter.val) point
          ((period : ℝ) * time)) := by
      change toroidal • rotationCLM time ((period : ℝ) • _) =
        rotationCLM time (((period : ℝ) * toroidal) • _)
      rw [← map_smul]
      congr 1
      rw [smul_smul]
      congr 1
      ring

theorem sampledPositionCoordinateValue_fderiv_allPoints
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (disk : Plane) (toroidal : ℝ) :
    fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter.val)
        (coordinateDirection point time) (coordinateDirection disk toroidal) =
      rotation time
        (fderiv ℝ (fun argument : Plane =>
          family.v (sampledEpsilon period) parameter.val argument
            ((period : ℝ) * time)) point disk +
          (((period : ℝ) * toroidal) •
            affineStateDerivative cellLength (sampledEpsilon period)
              (family.v (sampledEpsilon period) parameter.val) point
              ((period : ℝ) * time))) := by
  rw [coordinateDirection_add disk toroidal, map_add,
    sampledPositionCoordinateValue_fderiv_disk_allPoints cellLength family
      period epsilonIn parameter point pointIn time disk,
    sampledPositionCoordinateValue_fderiv_toroidal_allPoints cellLength family
      period periodPositive epsilonIn parameter point pointIn time toroidal]
  change rotationCLM time _ + rotationCLM time _ = rotationCLM time (_ + _)
  exact (map_add (rotationCLM time) _ _).symm

theorem rotation_injective (time : ℝ) :
    Function.Injective (rotation time) := by
  intro first second equality
  ext coordinate
  fin_cases coordinate
  · have coordinateZero := congrArg (fun point : Vec => point 0) equality
    have coordinateOne := congrArg (fun point : Vec => point 1) equality
    simp [rotation, vector] at coordinateZero coordinateOne
    calc
      first 0 = (Real.sin time ^ 2 + Real.cos time ^ 2) * first 0 := by
        rw [Real.sin_sq_add_cos_sq, one_mul]
      _ = Real.cos time *
            (Real.cos time * first 0 - Real.sin time * first 1) +
          Real.sin time *
            (Real.sin time * first 0 + Real.cos time * first 1) := by ring
      _ = Real.cos time *
            (Real.cos time * second 0 - Real.sin time * second 1) +
          Real.sin time *
            (Real.sin time * second 0 + Real.cos time * second 1) := by
        rw [coordinateZero, coordinateOne]
      _ = (Real.sin time ^ 2 + Real.cos time ^ 2) * second 0 := by ring
      _ = second 0 := by rw [Real.sin_sq_add_cos_sq, one_mul]
  · have coordinateZero := congrArg (fun point : Vec => point 0) equality
    have coordinateOne := congrArg (fun point : Vec => point 1) equality
    simp [rotation, vector] at coordinateZero coordinateOne
    calc
      first 1 = (Real.sin time ^ 2 + Real.cos time ^ 2) * first 1 := by
        rw [Real.sin_sq_add_cos_sq, one_mul]
      _ = -Real.sin time *
            (Real.cos time * first 0 - Real.sin time * first 1) +
          Real.cos time *
            (Real.sin time * first 0 + Real.cos time * first 1) := by ring
      _ = -Real.sin time *
            (Real.cos time * second 0 - Real.sin time * second 1) +
          Real.cos time *
            (Real.sin time * second 0 + Real.cos time * second 1) := by
        rw [coordinateZero, coordinateOne]
      _ = (Real.sin time ^ 2 + Real.cos time ^ 2) * second 1 := by ring
      _ = second 1 := by rw [Real.sin_sq_add_cos_sq, one_mul]
  · simpa [rotation, vector] using
      congrArg (fun point : Vec => point 2) equality

theorem sampledPositionCoordinateValue_fderiv_injective_of_bounds
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength)
    (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ)
    (bound : ℝ) (boundAtLeastOne : 1 ≤ bound)
    (errorSmall : family.bound * |sampledEpsilon period| <
      min (1 / 16) (cellLength / (64 * bound)))
    (timeColumnBound :
      ‖affineStateDerivative cellLength (sampledEpsilon period)
        (family.v (sampledEpsilon period) parameter.val) point
        ((period : ℝ) * time)‖ ≤ bound) :
    Function.Injective
      (fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter.val)
        (coordinateDirection point time)) := by
  let diskDerivative : Plane →L[ℝ] Vec := fderiv ℝ
    (fun argument : Plane =>
      family.v (sampledEpsilon period) parameter.val argument
        ((period : ℝ) * time)) point
  let timeColumn := affineStateDerivative cellLength (sampledEpsilon period)
    (family.v (sampledEpsilon period) parameter.val) point
    ((period : ℝ) * time)
  let error := family.bound * |sampledEpsilon period|
  have errorNonnegative : 0 ≤ error :=
    mul_nonneg (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _)
  have errorOne : error ≤ 1 := by
    have := lt_of_lt_of_le errorSmall (min_le_left _ _)
    dsimp [error]
    linarith
  have diskLower : ∀ direction : Plane,
      (1 / 8 : ℝ) * ‖direction‖ ≤ ‖diskDerivative direction‖ := by
    intro direction
    exact eighth_mul_norm_le_v_disk_fderiv cellLength family
      (sampledEpsilon period) epsilonIn parameter point pointIn
      ((period : ℝ) * time)
      (lt_of_lt_of_le errorSmall (min_le_left _ _)) direction
  have diskCoordinateUpper : ∀ direction : Plane,
      |(diskDerivative direction) 1| ≤ 2 * error * ‖direction‖ := by
    intro direction
    simpa [diskDerivative, error, mul_assoc] using
      abs_v_disk_fderiv_coordinate_one_le cellLength family
        (sampledEpsilon period) epsilonIn parameter point pointIn
        ((period : ℝ) * time) direction
  have timeColumnUpper : ‖timeColumn‖ ≤ bound := by
    simpa [timeColumn] using timeColumnBound
  have timeCoordinateClose : |timeColumn 1 - cellLength| ≤ 6 * error := by
    simpa [timeColumn, error] using
      abs_affineStateDerivative_coordinate_one_sub_cellLength_le cellLength
        family (sampledEpsilon period) epsilonIn parameter point pointIn
        ((period : ℝ) * time) errorOne
  have columnInjective : Function.Injective (fun argument : Plane × ℝ =>
      diskDerivative argument.1 +
        (((period : ℝ) * argument.2) • timeColumn)) :=
    cell_full_columns_injective_of_bounds cellLength cellLengthPositive
      period periodPositive diskDerivative timeColumn error bound
      errorNonnegative boundAtLeastOne (by simpa [error] using errorSmall)
      diskLower diskCoordinateUpper timeColumnUpper timeCoordinateClose
  intro first second derivativeEquality
  let firstCoordinates : Plane × ℝ := (planarPart first, first 2)
  let secondCoordinates : Plane × ℝ := (planarPart second, second 2)
  have firstIdentity : first =
      coordinateDirection firstCoordinates.1 firstCoordinates.2 := by
    ext coordinate
    fin_cases coordinate <;>
      simp [firstCoordinates, planarPart, coordinateDirection, vector]
  have secondIdentity : second =
      coordinateDirection secondCoordinates.1 secondCoordinates.2 := by
    ext coordinate
    fin_cases coordinate <;>
      simp [secondCoordinates, planarPart, coordinateDirection, vector]
  rw [firstIdentity, secondIdentity,
    sampledPositionCoordinateValue_fderiv_allPoints cellLength family period
      periodPositive epsilonIn parameter point pointIn time,
    sampledPositionCoordinateValue_fderiv_allPoints cellLength family period
      periodPositive epsilonIn parameter point pointIn time] at derivativeEquality
  have columnEquality := rotation_injective time derivativeEquality
  have coordinatesEqual : firstCoordinates = secondCoordinates := by
    apply columnInjective
    simpa [diskDerivative, timeColumn] using columnEquality
  rw [firstIdentity, secondIdentity, coordinatesEqual]

/-- A single sampling threshold makes the full three-dimensional derivative
of every sampled position chart injective at every closed-disk point and every
real lift of the toroidal coordinate. -/
theorem exists_sampledPositionFullDerivativeThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈
            Set.Ioo (-family.epsilonZero) family.epsilonZero ∧
          ∀ (parameter : Set.Icc family.lower family.upper)
            (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
            Function.Injective
              (fderiv ℝ
                (sampledPositionCoordinateValue cellLength family period
                  parameter.val)
                (coordinateDirection point time)) := by
  obtain ⟨bound, boundAtLeastOne, boundUpper⟩ :=
    exists_affineStateDerivative_bound cellLength cellLengthPositive family
  have boundPositive : 0 < bound := lt_of_lt_of_le zero_lt_one boundAtLeastOne
  let margin := min
    (min (1 / 16) (cellLength / (64 * bound)))
    (min (family.epsilonZero / 2) 1)
  have marginPositive : 0 < margin := by
    dsimp [margin]
    apply lt_min
    · apply lt_min
      · norm_num
      · exact div_pos cellLengthPositive (mul_pos (by norm_num) boundPositive)
    · exact lt_min (div_pos family.epsilonPositive (by norm_num)) zero_lt_one
  obtain ⟨firstPeriod, firstPositive, threshold⟩ :=
    exists_geometricSamplingThreshold cellLength cellLengthPositive family
      margin marginPositive 0
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter
  obtain ⟨epsilonIn, errorMargin, _radiusLarge⟩ :=
    threshold period periodAfter
  refine ⟨epsilonIn, ?_⟩
  have periodPositive : 0 < period :=
    lt_of_lt_of_le (Nat.zero_lt_of_lt firstPositive) periodAfter
  let error := family.bound * |sampledEpsilon period|
  have absoluteEpsilonLeError : |sampledEpsilon period| ≤ error := by
    dsimp [error]
    have scaled := mul_le_mul_of_nonneg_right family.boundAtLeastOne
      (abs_nonneg (sampledEpsilon period))
    simpa only [one_mul] using scaled
  have errorCore : error <
      min (1 / 16) (cellLength / (64 * bound)) :=
    (by simpa [error] using errorMargin.trans_le (min_le_left _ _))
  have epsilonDomain : |sampledEpsilon period| ≤ family.epsilonZero / 2 := by
    have errorUpper : error < family.epsilonZero / 2 :=
      errorMargin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    exact (absoluteEpsilonLeError.trans errorUpper.le)
  have epsilonUnit : |sampledEpsilon period| ≤ 1 := by
    have errorUpper : error < 1 :=
      errorMargin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    exact absoluteEpsilonLeError.trans errorUpper.le
  have errorOne : error ≤ 1 := by
    exact (lt_of_lt_of_le errorCore (min_le_left _ _)).le.trans (by norm_num)
  intro parameter point pointIn time
  apply sampledPositionCoordinateValue_fderiv_injective_of_bounds cellLength
    cellLengthPositive family period periodPositive epsilonIn parameter point
    pointIn time bound boundAtLeastOne
  · simpa [error] using errorCore
  · exact boundUpper (sampledEpsilon period) epsilonIn epsilonDomain
      epsilonUnit (by simpa [error] using errorOne) parameter point pointIn
      ((period : ℝ) * time)

/-- The Cartesian Jacobian of the sampled position lift, expressed as the
determinant of its ambient Fréchet derivative. -/
noncomputable def sampledPositionJacobian
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Vec) : ℝ :=
  LinearMap.det
    (fderiv ℝ
      (sampledPositionCoordinateValue cellLength family period parameter)
      point).toLinearMap

theorem sampledPositionJacobian_ne_zero_of_fderiv_injective
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (point : Vec)
    (derivativeInjective : Function.Injective
      (fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter)
        point)) :
    sampledPositionJacobian cellLength family period parameter point ≠ 0 := by
  intro determinantZero
  have kernelNontrivial : LinearMap.ker
      (fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter)
        point).toLinearMap ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp determinantZero
  exact kernelNontrivial (LinearMap.ker_eq_bot.mpr derivativeInjective)

/-- The exact public all-point immersion boundary: one integer threshold
simultaneously supplies injectivity of the sampled Cartesian derivative and a
nonzero Cartesian Jacobian, uniformly in the parameter, closed disk, and
toroidal lift. -/
theorem exists_sampledPositionImmersionDeterminantThreshold
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧
      ∀ period : ℕ, firstPeriod ≤ period →
        sampledEpsilon period ∈
            Set.Ioo (-family.epsilonZero) family.epsilonZero ∧
          ∀ (parameter : Set.Icc family.lower family.upper)
            (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
            Function.Injective
                (fderiv ℝ
                  (sampledPositionCoordinateValue cellLength family period
                    parameter.val)
                  (coordinateDirection point time)) ∧
              sampledPositionJacobian cellLength family period parameter.val
                (coordinateDirection point time) ≠ 0 := by
  obtain ⟨firstPeriod, firstPositive, threshold⟩ :=
    exists_sampledPositionFullDerivativeThreshold cellLength
      cellLengthPositive family
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period periodAfter
  obtain ⟨epsilonIn, derivativeThreshold⟩ := threshold period periodAfter
  refine ⟨epsilonIn, ?_⟩
  intro parameter point pointIn time
  have derivativeInjective := derivativeThreshold parameter point pointIn time
  exact ⟨derivativeInjective,
    sampledPositionJacobian_ne_zero_of_fderiv_injective cellLength family
      period parameter.val (coordinateDirection point time)
      derivativeInjective⟩

end Grad.PhysicalFamily.SampledFullGeometry
