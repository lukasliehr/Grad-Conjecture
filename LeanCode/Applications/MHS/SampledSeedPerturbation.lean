import SampledCellCoverDerivatives

noncomputable section

open Set Filter
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledGlobalEmbedding

open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledFullGeometry
open Grad.PhysicalFamily.SampledAllTimeBounds
open Grad.PhysicalFamily.SampledSeedBounds
open Grad.MainAssembly.PhysicalNormalHessian

def embeddingCellDomain (family : CellSolutionFamily cellLength) : Set CellArgument :=
  Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
    (Ioo family.parameterLower family.parameterUpper ×ˢ coordinateCollar family.collarRadius)

theorem embeddingCellDomain_isOpen (family : CellSolutionFamily cellLength) :
    IsOpen (embeddingCellDomain family) :=
  isOpen_Ioo.prod (isOpen_Ioo.prod (coordinateCollar_isOpen _))

def embeddingCompactArguments (family : CellSolutionFamily cellLength) : Set CellArgument :=
  Icc (-family.epsilonZero / 2) (family.epsilonZero / 2) ×ˢ
    (Icc family.lower family.upper ×ˢ
      ((fun argument : Plane × ℝ => coordinatePoint argument.1 argument.2) ''
        (Metric.closedBall (0 : Plane) 1 ×ˢ Icc (0 : ℝ) (2 * Real.pi))))

theorem embeddingCompactArguments_isCompact (family : CellSolutionFamily cellLength) :
    IsCompact (embeddingCompactArguments family) :=
  isCompact_Icc.prod (isCompact_Icc.prod
    (((isCompact_closedBall (0 : Plane) 1).prod isCompact_Icc).image
      coordinatePoint_uncurried_contDiff.continuous))

theorem embeddingCompactArguments_subset (family : CellSolutionFamily cellLength) :
    embeddingCompactArguments family ⊆ embeddingCellDomain family := by
  rintro ⟨epsilon, ⟨parameter, point⟩⟩
    ⟨epsilonIn, parameterIn, ⟨⟨disk, time⟩, ⟨diskIn, _⟩, rfl⟩⟩
  refine ⟨⟨by linarith [family.epsilonPositive, epsilonIn.1],
    by linarith [family.epsilonPositive, epsilonIn.2]⟩,
    ⟨lt_of_lt_of_le family.parameterContains.1 parameterIn.1,
      lt_of_le_of_lt parameterIn.2 family.parameterContains.2⟩, ?_⟩
  change ‖coordinateDisk (coordinatePoint disk time)‖ < family.collarRadius
  rw [coordinateDisk_coordinatePoint]
  have diskBound : ‖disk‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using diskIn
  exact lt_of_le_of_lt diskBound family.collarLarge

def embeddingCellJet (family : CellSolutionFamily cellLength) (argument : CellArgument) :
    Vec × (CellArgument →L[ℝ] Vec) :=
  (uncurriedCell family.v argument, fderiv ℝ (uncurriedCell family.v) argument)

theorem embeddingCellJet_contDiffOn (family : CellSolutionFamily cellLength) :
    ContDiffOn ℝ ∞ (embeddingCellJet family) (embeddingCellDomain family) := by
  exact family.vSmooth.prodMk
    (family.vSmooth.fderiv_of_isOpen (embeddingCellDomain_isOpen family) (by simp))

def cellArgumentEpsilonCLM : ℝ →L[ℝ] CellArgument :=
  ContinuousLinearMap.inl ℝ ℝ (ℝ × Vec)

@[simp] theorem cellArgumentEpsilonCLM_apply (epsilon : ℝ) :
    cellArgumentEpsilonCLM epsilon = (epsilon, (0, 0)) := rfl

theorem exists_embeddingCellJet_epsilon_bound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (epsilon : ℝ), |epsilon| ≤ family.epsilonZero / 2 →
        ∀ (parameter : Icc family.lower family.upper) (point : Plane), ‖point‖ ≤ 1 →
          ∀ (time : ℝ), time ∈ Icc (0 : ℝ) (2 * Real.pi) →
            ‖embeddingCellJet family (epsilon, (parameter.val, coordinatePoint point time)) -
              embeddingCellJet family (0, (parameter.val, coordinatePoint point time))‖ ≤
                bound * |epsilon| := by
  have jetSmooth := embeddingCellJet_contDiffOn family
  have jetDerivativeContinuous :=
    (jetSmooth.fderiv_of_isOpen (embeddingCellDomain_isOpen family)
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).continuousOn
  obtain ⟨rawBound, rawBoundUpper⟩ := (embeddingCompactArguments_isCompact family).bddAbove_image
    ((jetDerivativeContinuous.mono (embeddingCompactArguments_subset family)).norm)
  let bound := max 1 rawBound
  refine ⟨bound, le_max_left _ _, ?_⟩
  intro epsilon epsilonSmall parameter point pointIn time timeIn
  let insertion : ℝ → CellArgument := fun value =>
    (value, (parameter.val, coordinatePoint point time))
  have insertionDerivative (value : ℝ) :
      HasFDerivAt insertion cellArgumentEpsilonCLM value := by
    have derivative := cellArgumentEpsilonCLM.hasFDerivAt.add
      (hasFDerivAt_const (x := value) (0, (parameter.val, coordinatePoint point time)))
    have derivative' := derivative.congr_fderiv (add_zero cellArgumentEpsilonCLM)
    apply derivative'.congr_of_eventuallyEq
    filter_upwards [] with argument
    simp [insertion, cellArgumentEpsilonCLM_apply]
  have insertionCompact (value : ℝ)
      (valueIn : value ∈ Icc (-family.epsilonZero / 2) (family.epsilonZero / 2)) :
      insertion value ∈ embeddingCompactArguments family := by
    refine ⟨valueIn, parameter.property, ?_⟩
    exact ⟨(point, time), ⟨by simpa [Metric.mem_closedBall, dist_zero_right], timeIn⟩, rfl⟩
  have outerDifferentiable (value : ℝ)
      (valueIn : value ∈ Icc (-family.epsilonZero / 2) (family.epsilonZero / 2)) :
      DifferentiableAt ℝ (embeddingCellJet family) (insertion value) :=
    (jetSmooth.contDiffAt ((embeddingCellDomain_isOpen family).mem_nhds
      (embeddingCompactArguments_subset family (insertionCompact value valueIn))))
      |>.differentiableAt (by simp)
  have sectionDifferentiable (value : ℝ)
      (valueIn : value ∈ Icc (-family.epsilonZero / 2) (family.epsilonZero / 2)) :
      DifferentiableAt ℝ (embeddingCellJet family ∘ insertion) value :=
    (outerDifferentiable value valueIn).comp value
      (insertionDerivative value).differentiableAt
  have sectionBound (value : ℝ)
      (valueIn : value ∈ Icc (-family.epsilonZero / 2) (family.epsilonZero / 2)) :
      ‖deriv (embeddingCellJet family ∘ insertion) value‖ ≤ bound := by
    rw [deriv, fderiv_comp value (outerDifferentiable value valueIn)
      (insertionDerivative value).differentiableAt, (insertionDerivative value).fderiv]
    calc
      _ ≤ ‖fderiv ℝ (embeddingCellJet family) (insertion value)‖ *
          ‖cellArgumentEpsilonCLM 1‖ :=
        (fderiv ℝ (embeddingCellJet family) (insertion value)).le_opNorm _
      _ ≤ rawBound := by
        simpa [cellArgumentEpsilonCLM_apply] using
          rawBoundUpper ⟨insertion value, insertionCompact value valueIn, rfl⟩
      _ ≤ bound := le_max_right _ _
  have zeroIn : (0 : ℝ) ∈ Icc (-family.epsilonZero / 2) (family.epsilonZero / 2) :=
    ⟨by linarith [family.epsilonPositive], by linarith [family.epsilonPositive]⟩
  have epsilonIn : epsilon ∈ Icc (-family.epsilonZero / 2) (family.epsilonZero / 2) :=
    ⟨by linarith [(abs_le.mp epsilonSmall).1], (abs_le.mp epsilonSmall).2⟩
  have estimate := Convex.norm_image_sub_le_of_norm_deriv_le sectionDifferentiable
    sectionBound (convex_Icc _ _) zeroIn epsilonIn
  simpa [insertion] using estimate

theorem embeddingCellJet_periodic
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Plane) (pointIn : ‖point‖ ≤ 1) :
    Function.Periodic (fun time =>
      embeddingCellJet family (epsilon, (parameter.val, coordinatePoint point time)))
      (2 * Real.pi) := by
  intro time
  let base : CellArgument := (epsilon, (parameter.val, coordinatePoint point time))
  let shift : CellArgument → CellArgument := fun argument =>
    argument + cellArgumentTimeCLM (2 * Real.pi)
  have shiftIdentity : shift base =
      (epsilon, (parameter.val, coordinatePoint point (time + 2 * Real.pi))) := by
    apply Prod.ext
    · simp [shift, base, cellArgumentTimeCLM_apply]
    · apply Prod.ext
      · simp [shift, base, cellArgumentTimeCLM_apply]
      · ext coordinate
        fin_cases coordinate <;>
          simp [shift, base, cellArgumentTimeCLM_apply, coordinatePoint,
            tangentDirection, basisVector, vector]
  have shiftDerivative : HasFDerivAt shift (ContinuousLinearMap.id ℝ CellArgument) base := by
    have derivative := (hasFDerivAt_id (𝕜 := ℝ) base).add
      (hasFDerivAt_const (x := base) (cellArgumentTimeCLM (2 * Real.pi)))
    exact derivative.congr_fderiv (add_zero _)
  have baseIn (current : ℝ) :
      (epsilon, (parameter.val, coordinatePoint point current)) ∈ embeddingCellDomain family := by
    refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
    change ‖coordinateDisk (coordinatePoint point current)‖ < family.collarRadius
    rw [coordinateDisk_coordinatePoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have shiftedDifferentiable : DifferentiableAt ℝ (uncurriedCell family.v) (shift base) := by
    rw [shiftIdentity]
    exact (family.vSmooth.contDiffAt ((embeddingCellDomain_isOpen family).mem_nhds
      (baseIn (time + 2 * Real.pi)))).differentiableAt (by simp)
  have localEquality : uncurriedCell family.v ∘ shift =ᶠ[nhds base] uncurriedCell family.v := by
    filter_upwards [(embeddingCellDomain_isOpen family).mem_nhds (baseIn time)]
      with argument argumentIn
    have diskIn : coordinateDisk argument.2.2 ∈ Metric.ball (0 : Plane) family.collarRadius := by
      simpa [Metric.mem_ball, dist_zero_right, coordinateCollar] using argumentIn.2.2
    have periodic := family.vPeriodic argument.1 argumentIn.1 argument.2.1
      argumentIn.2.1 (coordinateDisk argument.2.2) diskIn (argument.2.2 1)
    simpa [shift, uncurriedCell, cellArgumentTimeCLM_apply, coordinateDisk,
      tangentDirection, basisVector, vector] using periodic
  have chain := (shiftedDifferentiable.hasFDerivAt.comp base shiftDerivative).fderiv
  rw [localEquality.fderiv_eq, shiftIdentity] at chain
  have derivativePeriodic :
      fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint point (time + 2 * Real.pi))) =
      fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint point time)) := by
    simpa [base] using chain.symm
  apply Prod.ext
  · simp only [embeddingCellJet, uncurriedCell, coordinateDisk_coordinatePoint]
    exact family.vPeriodic epsilon epsilonIn parameter.val
      (parameter_mem_open cellLength family parameter) point
      (closed_disk_mem_collar cellLength family point pointIn) time
  · exact derivativePeriodic

theorem exists_embeddingCellJet_epsilon_bound_allTime
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (epsilon : ℝ), epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero →
        |epsilon| ≤ family.epsilonZero / 2 →
        ∀ (parameter : Icc family.lower family.upper) (point : Plane), ‖point‖ ≤ 1 →
          ∀ (time : ℝ),
            ‖embeddingCellJet family (epsilon, (parameter.val, coordinatePoint point time)) -
              embeddingCellJet family (0, (parameter.val, coordinatePoint point time))‖ ≤
                bound * |epsilon| := by
  obtain ⟨bound, boundPositive, boundUpper⟩ := exists_embeddingCellJet_epsilon_bound cellLength family
  refine ⟨bound, boundPositive, ?_⟩
  intro epsilon epsilonIn epsilonSmall parameter point pointIn time
  have zeroIn : (0 : ℝ) ∈ Ioo (-family.epsilonZero) family.epsilonZero :=
    ⟨neg_neg_iff_pos.mpr family.epsilonPositive, family.epsilonPositive⟩
  rw [periodic_eq_fundamentalTime _
    (embeddingCellJet_periodic cellLength family epsilon epsilonIn parameter point pointIn) time,
    periodic_eq_fundamentalTime _
      (embeddingCellJet_periodic cellLength family 0 zeroIn parameter point pointIn) time]
  exact boundUpper epsilon epsilonSmall parameter point pointIn (fundamentalTime time)
    ⟨(fundamentalTime_mem_Ico time).1, (fundamentalTime_mem_Ico time).2.le⟩

def cellArgumentSpatialLinearMap : Vec →ₗ[ℝ] CellArgument where
  toFun argument := (0, (0, resampledCellPoint 1 argument))
  map_add' first second := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · ext coordinate
        fin_cases coordinate <;> simp [resampledCellPoint, vector]
  map_smul' scalar argument := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · ext coordinate
        fin_cases coordinate <;> simp [resampledCellPoint, vector]

def cellArgumentSpatialCLM : Vec →L[ℝ] CellArgument :=
  LinearMap.toContinuousLinearMap cellArgumentSpatialLinearMap

@[simp] theorem cellArgumentSpatialCLM_apply (argument : Vec) :
    cellArgumentSpatialCLM argument = (0, (0, resampledCellPoint 1 argument)) := rfl

theorem cellArgumentSpatialCLM_norm (argument : Vec) :
    ‖cellArgumentSpatialCLM argument‖ = ‖argument‖ := by
  have permutationNorm : ‖resampledCellPoint 1 argument‖ = ‖argument‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, resampledCellPoint, vector, Fin.sum_univ_three]
    ring
  simpa [cellArgumentSpatialCLM_apply] using permutationNorm

theorem cellCoverValue_fderiv_eq
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder) :
    fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val) point =
      (fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint (planarPart point) (point 2)))).comp
        cellArgumentSpatialCLM := by
  let insertion : Vec → CellArgument := fun argument =>
    (epsilon, (parameter.val, resampledCellPoint 1 argument))
  have insertionDerivative : HasFDerivAt insertion cellArgumentSpatialCLM point := by
    have derivative := (hasFDerivAt_const (x := point) (epsilon, (parameter.val, (0 : Vec)))).add
      cellArgumentSpatialCLM.hasFDerivAt
    have derivative' := derivative.congr_fderiv (zero_add cellArgumentSpatialCLM)
    apply derivative'.congr_of_eventuallyEq
    filter_upwards [] with argument
    simp [insertion, cellArgumentSpatialCLM_apply]
  have coordinateIdentity : resampledCellPoint 1 point =
      coordinatePoint (planarPart point) (point 2) := by
    ext coordinate
    fin_cases coordinate <;> simp [resampledCellPoint, coordinatePoint, planarPart, vector]
  have insertionIn : insertion point ∈ embeddingCellDomain family := by
    refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
    change ‖coordinateDisk (resampledCellPoint 1 point)‖ < family.collarRadius
    rw [coordinateDisk_resampledCellPoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have outer := (family.vSmooth.contDiffAt
    ((embeddingCellDomain_isOpen family).mem_nhds insertionIn)).differentiableAt (by simp)
  have chain := (outer.hasFDerivAt.comp point insertionDerivative).fderiv
  have functionIdentity : uncurriedCell family.v ∘ insertion =
      cellCoverValue cellLength family epsilon parameter.val := by
    funext argument
    simp [insertion, uncurriedCell, cellCoverValue]
  rw [functionIdentity] at chain
  simpa only [insertion, coordinateIdentity] using chain

theorem exists_cellCoverPerturbation_bounds
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    ∃ bound : ℝ, 1 ≤ bound ∧
      ∀ (epsilon : ℝ), epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero →
        |epsilon| ≤ family.epsilonZero / 2 →
        ∀ (parameter : Icc family.lower family.upper) (point : Vec), point ∈ cylinder →
          ‖cellCoverValue cellLength family epsilon parameter.val point -
            cellCoverValue cellLength family 0 parameter.val point‖ ≤ bound * |epsilon| ∧
          ‖fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val) point -
            fderiv ℝ (cellCoverValue cellLength family 0 parameter.val) point‖ ≤
              bound * |epsilon| := by
  obtain ⟨bound, boundPositive, boundUpper⟩ :=
    exists_embeddingCellJet_epsilon_bound_allTime cellLength family
  refine ⟨bound, boundPositive, ?_⟩
  intro epsilon epsilonIn epsilonSmall parameter point pointIn
  have estimate := boundUpper epsilon epsilonIn epsilonSmall parameter
    (planarPart point) pointIn (point 2)
  change max
      ‖uncurriedCell family.v (epsilon, (parameter.val, coordinatePoint (planarPart point) (point 2))) -
        uncurriedCell family.v (0, (parameter.val, coordinatePoint (planarPart point) (point 2)))‖
      ‖fderiv ℝ (uncurriedCell family.v)
          (epsilon, (parameter.val, coordinatePoint (planarPart point) (point 2))) -
        fderiv ℝ (uncurriedCell family.v)
          (0, (parameter.val, coordinatePoint (planarPart point) (point 2)))‖ ≤
      bound * |epsilon| at estimate
  have estimates := max_le_iff.mp estimate
  constructor
  · have valueBound := estimates.1
    simp only [uncurriedCell, coordinateDisk_coordinatePoint] at valueBound
    exact valueBound
  · have zeroIn : (0 : ℝ) ∈ Ioo (-family.epsilonZero) family.epsilonZero :=
      ⟨neg_neg_iff_pos.mpr family.epsilonPositive, family.epsilonPositive⟩
    rw [cellCoverValue_fderiv_eq cellLength family epsilon epsilonIn parameter point pointIn,
      cellCoverValue_fderiv_eq cellLength family 0 zeroIn parameter point pointIn]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    change ‖(fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint (planarPart point) (point 2))) -
      fderiv ℝ (uncurriedCell family.v)
        (0, (parameter.val, coordinatePoint (planarPart point) (point 2))))
          (cellArgumentSpatialCLM direction)‖ ≤ _
    exact ((fderiv ℝ (uncurriedCell family.v)
        (epsilon, (parameter.val, coordinatePoint (planarPart point) (point 2))) -
      fderiv ℝ (uncurriedCell family.v)
        (0, (parameter.val, coordinatePoint (planarPart point) (point 2)))).le_opNorm
          (cellArgumentSpatialCLM direction)).trans (by
            rw [cellArgumentSpatialCLM_norm]
            exact mul_le_mul_of_nonneg_right estimates.2 (norm_nonneg _))

theorem cellCoverValue_zero_eq_seed
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (parameter : Icc family.lower family.upper) (point : Vec) (pointIn : point ∈ cylinder) :
    cellCoverValue cellLength family 0 parameter.val point =
      planeEmbedding (seedAction family.rho family.alpha family.delta parameter.val
        (point 2) (planarPart point)) := by
  have zeroIn : (0 : ℝ) ∈ Ioo (-family.epsilonZero) family.epsilonZero :=
    ⟨neg_neg_iff_pos.mpr family.epsilonPositive, family.epsilonPositive⟩
  have tiltZero : family.tilt 0 parameter.val (point 2) = 0 := by
    have estimate := tilt_value_norm_le_physicalBound_allTime cellLength family 0 zeroIn
      parameter (point 2)
    simpa using norm_eq_zero.mp (le_antisymm (by simpa using estimate) (norm_nonneg _))
  have remainderZero : family.remainder 0 parameter.val (planarPart point) (point 2) = 0 := by
    have estimate := remainder_value_norm_le_physicalBound_allTime cellLength family 0 zeroIn
      parameter (planarPart point) pointIn (point 2)
    exact norm_eq_zero.mp (le_antisymm (by simpa using estimate) (norm_nonneg _))
  rw [cellCoverValue, family.normalizedChart 0 zeroIn parameter.val parameter.property
    (planarPart point) pointIn (point 2), tiltZero, remainderZero]
  simp [normalizedFactor, planeDot]

end Grad.PhysicalFamily.SampledGlobalEmbedding
