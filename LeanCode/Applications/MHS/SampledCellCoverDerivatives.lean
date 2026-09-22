import SampledCylindricalEstimates

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledGlobalEmbedding

open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledFullGeometry
open Grad.PhysicalFamily.SampledAllTimeBounds
open Grad.PhysicalFamily.SampledSeedBounds
open Grad.PhysicalFamily.SampledPositionDerivative
open Grad.PhysicalFamily.SampledNormalizedFactorBounds
open Grad.MainAssembly.SampledAxisBasics
open Grad.MainAssembly.PhysicalNormalHessian

@[simp] theorem planarPart_coordinateDirection (point : Plane) (time : ℝ) :
    planarPart (coordinateDirection point time) = point := by
  ext coordinate
  fin_cases coordinate <;> simp [planarPart, coordinateDirection, vector]

@[simp] theorem coordinateDirection_time (point : Plane) (time : ℝ) :
    (coordinateDirection point time) 2 = time := by
  simp [coordinateDirection, vector]

@[simp] theorem coordinateDirection_planarPart (point : Vec) :
    coordinateDirection (planarPart point) (point 2) = point := by
  ext coordinate
  fin_cases coordinate <;> simp [coordinateDirection, planarPart, vector]

theorem planarPart_norm_le (point : Vec) : ‖planarPart point‖ ≤ ‖point‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, planarPart,
    Fin.sum_univ_two, Fin.sum_univ_three]
  positivity

def cellCoverValue (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon parameter : ℝ) (argument : Vec) : Vec :=
  family.v epsilon parameter (planarPart argument) (argument 2)

theorem cellCoverValue_differentiableAt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec)
    (pointIn : point ∈ cylinder) :
    DifferentiableAt ℝ (cellCoverValue cellLength family epsilon parameter.val) point := by
  let insertion : Vec → CellArgument := fun argument =>
    (epsilon, (parameter.val, resampledCellPoint 1 argument))
  have insertionSmooth : ContDiff ℝ ∞ insertion :=
    contDiff_const.prodMk (contDiff_const.prodMk (resampledCellPoint_contDiff 1))
  have insertionIn : insertion point ∈
      Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) := by
    refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
    change ‖coordinateDisk (resampledCellPoint 1 point)‖ < family.collarRadius
    rw [coordinateDisk_resampledCellPoint]
    exact lt_of_le_of_lt pointIn family.collarLarge
  have outer := (family.vSmooth.contDiffAt
    ((isOpen_Ioo.prod (isOpen_Ioo.prod (coordinateCollar_isOpen _))).mem_nhds
      insertionIn)).differentiableAt (by simp)
  have composed := outer.comp point
    (insertionSmooth.differentiable (by simp)).differentiableAt
  have functionIdentity : uncurriedCell family.v ∘ insertion =
      cellCoverValue cellLength family epsilon parameter.val := by
    funext argument
    simp [insertion, uncurriedCell, cellCoverValue]
  rw [functionIdentity] at composed
  exact composed

theorem jointCell_fderiv_apply
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (mapping : Plane → ℝ → Target) (point : Vec)
    (mappingDifferentiable : DifferentiableAt ℝ
      (fun argument : Vec => mapping (planarPart argument) (argument 2)) point)
    (direction : Vec) :
    fderiv ℝ (fun argument : Vec => mapping (planarPart argument) (argument 2))
        point direction =
      fderiv ℝ (fun disk => mapping disk (point 2)) (planarPart point)
          (planarPart direction) +
        (direction 2) • cellDerivative mapping (planarPart point) (point 2) := by
  let joint := fun argument : Vec => mapping (planarPart argument) (argument 2)
  let diskInsertion : Plane → Vec := fun disk =>
    coordinateDirection disk (point 2)
  have diskInsertionDerivative : HasFDerivAt diskInsertion physicalDiskCLM
      (planarPart point) := by
    have result := (hasFDerivAt_const (x := planarPart point)
      (coordinateDirection (0 : Plane) (point 2))).add physicalDiskCLM.hasFDerivAt
    have result' := result.congr_fderiv (zero_add physicalDiskCLM)
    apply result'.congr_of_eventuallyEq
    filter_upwards [] with disk
    ext coordinate
    fin_cases coordinate <;>
      simp [diskInsertion, physicalDiskCLM_apply, coordinateDirection, vector]
  have diskBase : diskInsertion (planarPart point) = point := by simp [diskInsertion]
  have diskOuter : HasFDerivAt joint (fderiv ℝ joint point)
      (diskInsertion (planarPart point)) := by
    rw [diskBase]
    exact mappingDifferentiable.hasFDerivAt
  have diskChain := diskOuter.comp (planarPart point) diskInsertionDerivative
  have diskChain' : HasFDerivAt (fun disk => mapping disk (point 2))
      ((fderiv ℝ joint point).comp physicalDiskCLM) (planarPart point) := by
    simpa [Function.comp_def, diskInsertion, joint] using diskChain
  have diskIdentity := congrArg (fun derivative : Plane →L[ℝ] Target =>
    derivative (planarPart direction)) diskChain'.fderiv
  let timeInsertion : ℝ → Vec := fun time =>
    coordinateDirection (planarPart point) time
  have timeInsertionDerivative : HasFDerivAt timeInsertion physicalToroidalCLM
      (point 2) := by
    have result := (hasFDerivAt_const (x := point 2)
      (coordinateDirection (planarPart point) 0)).add physicalToroidalCLM.hasFDerivAt
    have result' := result.congr_fderiv (zero_add physicalToroidalCLM)
    apply result'.congr_of_eventuallyEq
    filter_upwards [] with time
    ext coordinate
    fin_cases coordinate <;>
      simp [timeInsertion, physicalToroidalCLM_apply, coordinateDirection, vector]
  have timeBase : timeInsertion (point 2) = point := by simp [timeInsertion]
  have timeOuter : HasFDerivAt joint (fderiv ℝ joint point)
      (timeInsertion (point 2)) := by
    rw [timeBase]
    exact mappingDifferentiable.hasFDerivAt
  have timeChain := timeOuter.comp (point 2) timeInsertionDerivative
  have timeChain' : HasFDerivAt (mapping (planarPart point))
      ((fderiv ℝ joint point).comp physicalToroidalCLM) (point 2) := by
    simpa [Function.comp_def, timeInsertion, joint] using timeChain
  have timeIdentity := congrArg (fun derivative : ℝ →L[ℝ] Target =>
    derivative (direction 2)) timeChain'.fderiv
  have scalarIdentity :
      fderiv ℝ (mapping (planarPart point)) (point 2) (direction 2) =
        (direction 2) • cellDerivative mapping (planarPart point) (point 2) := by
    rw [cellDerivative, ← map_smul]
    simp
  rw [scalarIdentity] at timeIdentity
  change _ = fderiv ℝ joint point (coordinateDirection (planarPart direction) 0)
    at diskIdentity
  change _ = fderiv ℝ joint point (coordinateDirection (0 : Plane) (direction 2))
    at timeIdentity
  rw [diskIdentity, timeIdentity, ← map_add]
  change fderiv ℝ joint point direction = _
  congr 1
  ext coordinate
  fin_cases coordinate <;> simp [coordinateDirection, planarPart, vector]

theorem cellCoverCoordinate_hasFDerivAt
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec)
    (pointIn : point ∈ cylinder) (coordinate : Fin 3) :
    HasFDerivAt (fun argument =>
      (cellCoverValue cellLength family epsilon parameter.val argument) coordinate)
      ((vecCoordinateCLM coordinate).comp
        (fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val) point)) point := by
  exact (vecCoordinateCLM coordinate).hasFDerivAt.comp point
    (cellCoverValue_differentiableAt cellLength family epsilon epsilonIn
      parameter point pointIn).hasFDerivAt

theorem cellCoverValue_tangential_fderiv_bound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Vec)
    (pointIn : point ∈ cylinder) :
    ‖(vecCoordinateCLM 1).comp
      (fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val) point)‖ ≤
        4 * (family.bound * |epsilon|) := by
  have errorNonnegative : 0 ≤ family.bound * |epsilon| :=
    mul_nonneg (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  change |(fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val)
    point direction) 1| ≤ _
  rw [show cellCoverValue cellLength family epsilon parameter.val =
    (fun argument : Vec => family.v epsilon parameter.val
      (planarPart argument) (argument 2)) by rfl]
  rw [jointCell_fderiv_apply (family.v epsilon parameter.val) point
    (cellCoverValue_differentiableAt cellLength family epsilon epsilonIn
      parameter point pointIn) direction]
  change |(fderiv ℝ (fun disk => family.v epsilon parameter.val disk (point 2))
      (planarPart point) (planarPart direction)) 1 +
    direction 2 * (cellDerivative (family.v epsilon parameter.val)
      (planarPart point) (point 2)) 1| ≤ _
  calc
    _ ≤ |(fderiv ℝ (fun disk => family.v epsilon parameter.val disk (point 2))
        (planarPart point) (planarPart direction)) 1| +
      |direction 2 * (cellDerivative (family.v epsilon parameter.val)
        (planarPart point) (point 2)) 1| := abs_add_le _ _
    _ ≤ (2 * (family.bound * |epsilon|)) * ‖planarPart direction‖ +
        |direction 2| * (2 * (family.bound * |epsilon|)) := by
      rw [abs_mul]
      exact add_le_add
        (abs_v_disk_fderiv_coordinate_one_le cellLength family epsilon epsilonIn
          parameter (planarPart point) pointIn (point 2) (planarPart direction))
        (mul_le_mul_of_nonneg_left
          (abs_v_cellDerivative_coordinate_one_le cellLength family epsilon
            epsilonIn parameter (planarPart point) pointIn (point 2)) (abs_nonneg _))
    _ ≤ (2 * (family.bound * |epsilon|)) * ‖direction‖ +
        ‖direction‖ * (2 * (family.bound * |epsilon|)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (planarPart_norm_le direction) (by positivity))
        (mul_le_mul_of_nonneg_right (coordinate_abs_le_norm direction 2) (by positivity))
    _ = _ := by ring

theorem v_disk_fderiv_apply_norm_le_four
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ) (epsilonIn : epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Icc family.lower family.upper) (point : Plane) (pointIn : ‖point‖ ≤ 1)
    (time : ℝ) (errorSmall : family.bound * |epsilon| ≤ 1) (direction : Plane) :
    ‖fderiv ℝ (fun disk => family.v epsilon parameter.val disk time) point direction‖ ≤
      4 * ‖direction‖ := by
  rw [v_fderiv_closedDisk_eq_axis_add_remainder cellLength family epsilon epsilonIn
    parameter time point pointIn, add_apply, cellAxisCLM_apply]
  have factorNonnegative := normalizedFactor_nonnegative (family.tilt epsilon parameter.val time)
  have factorLe := normalizedFactor_le_one (family.tilt epsilon parameter.val time)
    (family.tiltBound epsilon epsilonIn parameter.val parameter.property time)
  have tiltLe := (tilt_value_norm_le_physicalBound_allTime cellLength family epsilon
    epsilonIn parameter time).trans errorSmall
  have seedBound : ‖seedAction family.rho family.alpha family.delta parameter.val
      time direction‖ ≤ 2 * ‖direction‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have bound := seedAction_norm_sq_le family.rho family.alpha family.delta
      parameter.val time direction family.rhoPositive.le (by linarith [family.rhoSmall])
    have rhoLe : 1 + family.rho ≤ 4 := by linarith [family.rhoSmall]
    have scaled := mul_le_mul_of_nonneg_right rhoLe (sq_nonneg ‖direction‖)
    nlinarith
  have remainderBound := remainder_disk_fderiv_apply_norm_le_physicalBound_allTime
    cellLength family epsilon epsilonIn parameter point pointIn time direction
  calc
    _ ≤ ‖normalizedFactor (family.tilt epsilon parameter.val time) •
        planeEmbedding (seedAction family.rho family.alpha family.delta parameter.val time direction)‖ +
      ‖planeDot (family.tilt epsilon parameter.val time) direction • tangentDirection‖ +
      ‖fderiv ℝ (fun disk => family.remainder epsilon parameter.val disk time) point direction‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 1 * (2 * ‖direction‖) + (1 * ‖direction‖) * 1 + 1 * ‖direction‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg factorNonnegative,
        planeEmbedding_norm, norm_smul, Real.norm_eq_abs, tangentDirection_norm]
      apply add_le_add
      · exact add_le_add (mul_le_mul factorLe seedBound (norm_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_right
            ((abs_planeDot_le_norm_mul_norm _ _).trans
              (mul_le_mul_of_nonneg_right tiltLe (norm_nonneg _))) zero_le_one)
      · exact remainderBound.trans (mul_le_mul_of_nonneg_right errorSmall (norm_nonneg _))
    _ = _ := by ring

theorem exists_cellCoverValue_fderiv_bound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength) :
    ∃ derivativeBound : ℝ, 1 ≤ derivativeBound ∧
      ∀ (epsilon : ℝ), epsilon ∈ Ioo (-family.epsilonZero) family.epsilonZero →
        |epsilon| ≤ family.epsilonZero / 2 → family.bound * |epsilon| ≤ 1 →
        ∀ (parameter : Icc family.lower family.upper) (point : Vec), point ∈ cylinder →
          ‖fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val) point‖ ≤
            derivativeBound := by
  obtain ⟨timeBound, timeBoundPositive, timeBoundUpper⟩ :=
    exists_v_cellDerivative_bound cellLength family
  refine ⟨4 + timeBound, by linarith, ?_⟩
  intro epsilon epsilonIn epsilonSmall errorSmall parameter point pointIn
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro direction
  rw [show cellCoverValue cellLength family epsilon parameter.val =
    (fun argument : Vec => family.v epsilon parameter.val
      (planarPart argument) (argument 2)) by rfl]
  rw [jointCell_fderiv_apply (family.v epsilon parameter.val) point
    (cellCoverValue_differentiableAt cellLength family epsilon epsilonIn
      parameter point pointIn) direction]
  calc
    _ ≤ ‖fderiv ℝ (fun disk => family.v epsilon parameter.val disk (point 2))
        (planarPart point) (planarPart direction)‖ +
      ‖direction 2 • cellDerivative (family.v epsilon parameter.val)
        (planarPart point) (point 2)‖ := norm_add_le _ _
    _ ≤ 4 * ‖planarPart direction‖ + |direction 2| * timeBound := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (v_disk_fderiv_apply_norm_le_four cellLength family epsilon epsilonIn
          parameter (planarPart point) pointIn (point 2) errorSmall (planarPart direction))
        (mul_le_mul_of_nonneg_left
          (timeBoundUpper epsilon epsilonIn epsilonSmall parameter
            (planarPart point) pointIn (point 2)) (abs_nonneg _))
    _ ≤ 4 * ‖direction‖ + ‖direction‖ * timeBound :=
      add_le_add (mul_le_mul_of_nonneg_left (planarPart_norm_le _) (by norm_num))
        (mul_le_mul_of_nonneg_right (coordinate_abs_le_norm direction 2) (by linarith))
    _ = _ := by ring

theorem vecCoordinateCLM_comp_norm_le (coordinate : Fin 3)
    (derivative : Vec →L[ℝ] Vec) :
    ‖(vecCoordinateCLM coordinate).comp derivative‖ ≤ ‖derivative‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro direction
  exact (coordinate_abs_le_norm (derivative direction) coordinate).trans
    (derivative.le_opNorm direction)

def sampledScaledAngle (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (argument : Vec) : ℝ :=
  (period : ℝ) * sampledCylindricalAngleCorrection cellLength family period
    parameter (planarPart argument) (argument 2)

def sampledRadialCorrection (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (period : ℕ) (parameter : ℝ) (argument : Vec) : ℝ :=
  sampledCylindricalRadius cellLength family period parameter (planarPart argument)
    (argument 2) - ((period : ℝ) * cellLength +
      cellCoverValue cellLength family (sampledEpsilon period) parameter argument 0)

/-- Actual family specialization of the angular estimate and radial correction.
The one constant is uniform in N, the compact family parameter, and every
point of the closed universal cylinder. -/
theorem exists_sampledCylindricalCorrection_bounds
    (cellLength : ℝ) (cellLengthPositive : 0 < cellLength)
    (family : CellSolutionFamily cellLength) :
    ∃ derivativeBound : ℝ, 1 ≤ derivativeBound ∧
      ∀ (period : ℕ), 0 < period →
        ∀ (_epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero),
        |sampledEpsilon period| ≤ family.epsilonZero / 2 →
        4 * (family.bound * |sampledEpsilon period|) ≤ 1 →
        8 ≤ (period : ℝ) * cellLength →
        ∀ (parameter : Icc family.lower family.upper) (point : Vec), point ∈ cylinder →
          |sampledScaledAngle cellLength family period parameter.val point| ≤
              (4 * (2 + 4 * derivativeBound) / cellLength) *
                (family.bound * |sampledEpsilon period|) ∧
          ‖fderiv ℝ (sampledScaledAngle cellLength family period parameter.val) point‖ ≤
              (4 * (2 + 4 * derivativeBound) / cellLength) *
                (family.bound * |sampledEpsilon period|) ∧
          |sampledRadialCorrection cellLength family period parameter.val point| ≤
              (4 * (2 * derivativeBound + 2)) *
                (family.bound * |sampledEpsilon period|) ∧
          ‖fderiv ℝ (sampledRadialCorrection cellLength family period parameter.val) point‖ ≤
              (4 * (2 * derivativeBound + 2)) *
                (family.bound * |sampledEpsilon period|) := by
  obtain ⟨derivativeBound, derivativeBoundPositive, derivativeBoundUpper⟩ :=
    exists_cellCoverValue_fderiv_bound cellLength family
  refine ⟨derivativeBound, derivativeBoundPositive, ?_⟩
  intro period periodPositive epsilonIn epsilonSmall errorSmall radiusLarge parameter point pointIn
  let epsilon := sampledEpsilon period
  let error := family.bound * |epsilon|
  let radial : Vec → ℝ := fun argument => (period : ℝ) * cellLength +
    cellCoverValue cellLength family epsilon parameter.val argument 0
  let tangential : Vec → ℝ := fun argument =>
    cellCoverValue cellLength family epsilon parameter.val argument 1
  let radialDerivative := (vecCoordinateCLM 0).comp
    (fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val) point)
  let tangentialDerivative := (vecCoordinateCLM 1).comp
    (fderiv ℝ (cellCoverValue cellLength family epsilon parameter.val) point)
  have errorNonnegative : 0 ≤ error :=
    mul_nonneg (le_trans zero_le_one family.boundAtLeastOne) (abs_nonneg _)
  have errorLe : error ≤ 1 := by change 4 * error ≤ 1 at errorSmall; linarith
  have radialHasDerivative : HasFDerivAt radial radialDerivative point := by
    have derivative :=
      (hasFDerivAt_const (x := point) ((period : ℝ) * cellLength)).add
        (cellCoverCoordinate_hasFDerivAt cellLength family epsilon epsilonIn
          parameter point pointIn 0)
    exact derivative.congr_fderiv (zero_add radialDerivative)
  have tangentialHasDerivative : HasFDerivAt tangential tangentialDerivative point :=
    cellCoverCoordinate_hasFDerivAt cellLength family epsilon epsilonIn
      parameter point pointIn 1
  have radialLower : (period : ℝ) * cellLength / 2 ≤ radial point := by
    have valueBound := v_norm_le_four cellLength family epsilon epsilonIn parameter
      (planarPart point) pointIn (point 2) errorLe
    have coordinateBound := (coordinate_abs_le_norm
      (family.v epsilon parameter.val (planarPart point) (point 2)) 0).trans valueBound
    dsimp [radial, cellCoverValue]
    linarith [(abs_le.mp coordinateBound).1]
  have radialBound : ‖radialDerivative‖ ≤ derivativeBound :=
    (vecCoordinateCLM_comp_norm_le 0 _).trans
      (derivativeBoundUpper epsilon epsilonIn epsilonSmall errorLe parameter point pointIn)
  have tangentialValue : |tangential point| ≤ 4 * error := by
    have valueBound := sampled_v_tangential_abs_le_two_error cellLength family epsilon
      epsilonIn parameter (planarPart point) pointIn (point 2)
    change |tangential point| ≤ 2 * error at valueBound
    linarith
  have tangentialBound : ‖tangentialDerivative‖ ≤ 4 * error :=
    cellCoverValue_tangential_fderiv_bound cellLength family epsilon epsilonIn
      parameter point pointIn
  have angular := cylindricalAngle_value_fderiv_bound radial tangential point
    radialDerivative tangentialDerivative radialHasDerivative tangentialHasDerivative
    period cellLength (4 * error) derivativeBound (Nat.cast_pos.mpr periodPositive)
    cellLengthPositive (by linarith) radialLower (by positivity)
    tangentialValue tangentialBound radialBound
  have radialEstimate := cylindricalRadialCorrection_value_fderiv_bound radial tangential point
    radialDerivative tangentialDerivative radialHasDerivative tangentialHasDerivative
    ((period : ℝ) * cellLength) (4 * error) derivativeBound (by linarith)
    radialLower (by positivity) errorSmall tangentialValue tangentialBound radialBound
  have angularFunction : (fun argument => (period : ℝ) *
      Real.arctan (tangential argument / radial argument)) =
      sampledScaledAngle cellLength family period parameter.val := rfl
  have radialFunction : (fun argument =>
      Real.sqrt (radial argument ^ 2 + tangential argument ^ 2) - radial argument) =
      sampledRadialCorrection cellLength family period parameter.val := rfl
  have angularConstant : ((2 + 4 * derivativeBound) / cellLength) * (4 * error) =
      (4 * (2 + 4 * derivativeBound) / cellLength) * error := by ring
  have radialConstant : (2 * derivativeBound + 2) * (4 * error) =
      (4 * (2 * derivativeBound + 2)) * error := by ring
  rw [angularFunction, angularConstant] at angular
  have radialValue := radialEstimate.2.2.1
  have radialDerivativeEstimate := radialEstimate.2.2.2
  rw [radialFunction, radialConstant] at radialDerivativeEstimate
  rw [radialConstant] at radialValue
  exact ⟨angular.1, angular.2, radialValue, radialDerivativeEstimate⟩

end Grad.PhysicalFamily.SampledGlobalEmbedding
