import SampledSmoothFamily
import Mathlib.Topology.MetricSpace.ProperSpace.Real

noncomputable section

open Set
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledSeminormBounds

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily

private def cellEvaluationDomain : Set Vec :=
  (fun argument : Plane × ℝ => coordinatePoint argument.1 argument.2) ''
    (Metric.closedBall (0 : Plane) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))

private theorem cellEvaluationDomain_isCompact :
    IsCompact cellEvaluationDomain := by
  exact ((isCompact_closedBall (0 : Plane) 1).prod isCompact_Icc).image
    coordinatePoint_uncurried_contDiff.continuous

private theorem cellEvaluationDomain_subset_collar
    (family : CellSolutionFamily cellLength) :
    cellEvaluationDomain ⊆ coordinateCollar family.collarRadius := by
  rintro point ⟨⟨disk, time⟩, ⟨diskIn, _⟩, rfl⟩
  change ‖coordinateDisk (coordinatePoint disk time)‖ < family.collarRadius
  rw [coordinateDisk_coordinatePoint]
  have diskNorm : ‖disk‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using diskIn
  exact lt_of_le_of_lt diskNorm family.collarLarge

private theorem fixedRemainder_contDiffOn
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) :
    ContDiffOn ℝ ∞
      (fun argument : Vec => family.remainder epsilon parameter.val
        (coordinateDisk argument) (argument 1))
      (coordinateCollar family.collarRadius) := by
  let insertion : Vec → CellArgument := fun argument =>
    (epsilon, (parameter.val, argument))
  have insertionSmooth : ContDiff ℝ ∞ insertion := by
    dsimp [insertion]
    fun_prop
  simpa [Function.comp_def, insertion, uncurriedCell] using
    family.remainderSmooth.comp insertionSmooth.contDiffOn (by
      intro argument argumentIn
      exact ⟨epsilonIn, parameter_mem_open cellLength family parameter,
        argumentIn⟩)

private theorem remainder_order_image_bddAbove
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (order : Fin 3) :
    BddAbove
      ((fun point : Vec =>
        ‖iteratedFDeriv ℝ order.val
          (fun argument : Vec => family.remainder epsilon parameter.val
            (coordinateDisk argument) (argument 1)) point‖) ''
        cellEvaluationDomain) := by
  apply cellEvaluationDomain_isCompact.bddAbove_image
  have derivativeContinuous : ContinuousOn
      (iteratedFDeriv ℝ order.val
        (fun argument : Vec => family.remainder epsilon parameter.val
          (coordinateDisk argument) (argument 1)))
      (coordinateCollar family.collarRadius) :=
    ContinuousOn.continuousOn_iteratedFDeriv
      (fixedRemainder_contDiffOn cellLength family epsilon epsilonIn parameter)
      (coordinateCollar_isOpen _)
      (show (order.val : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)
  exact (derivativeContinuous.mono
    (cellEvaluationDomain_subset_collar family)).norm

theorem remainder_cellC2_values_bddAbove
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) :
    BddAbove {value : ℝ |
      ∃ (order : Fin 3) (point : Plane) (time : ℝ),
        ‖point‖ ≤ 1 ∧ time ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
        value = ‖iteratedFDeriv ℝ order.val
          (fun argument : Vec => family.remainder epsilon parameter.val
            (coordinateDisk argument) (argument 1))
          (coordinatePoint point time)‖} := by
  classical
  choose bound boundUpper using fun order : Fin 3 =>
    remainder_order_image_bddAbove cellLength family epsilon epsilonIn
      parameter order
  let totalBound : ℝ := ∑ order : Fin 3, max 0 (bound order)
  refine ⟨totalBound, ?_⟩
  rintro value ⟨order, point, time, pointIn, timeIn, rfl⟩
  have evaluationIn : coordinatePoint point time ∈ cellEvaluationDomain := by
    refine ⟨(point, time), ?_, rfl⟩
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right], timeIn⟩
  have valueLe :
      ‖iteratedFDeriv ℝ order.val
        (fun argument : Vec => family.remainder epsilon parameter.val
          (coordinateDisk argument) (argument 1))
        (coordinatePoint point time)‖ ≤ bound order :=
    boundUpper order ⟨coordinatePoint point time, evaluationIn, rfl⟩
  exact valueLe.trans ((le_max_right 0 (bound order)).trans
    (Finset.single_le_sum (fun index _ => le_max_left 0 (bound index))
      (Finset.mem_univ order)))

theorem remainder_iteratedFDeriv_le_cellC2Seminorm
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (order : Fin 3) (point : Plane) (pointIn : ‖point‖ ≤ 1)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖iteratedFDeriv ℝ order.val
      (fun argument : Vec => family.remainder epsilon parameter.val
        (coordinateDisk argument) (argument 1))
      (coordinatePoint point time)‖ ≤
      cellC2Seminorm (family.remainder epsilon parameter.val) := by
  apply le_csSup
    (remainder_cellC2_values_bddAbove cellLength family epsilon epsilonIn
      parameter)
  exact ⟨order, point, time, pointIn, timeIn, rfl⟩

private theorem fixedTilt_contDiff
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
  have insertionIn : insertion time ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ Set.univ) :=
    ⟨epsilonIn, parameter_mem_open cellLength family parameter,
      Set.mem_univ time⟩
  have domainOpen : IsOpen
      (Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ Set.univ)) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod
      (isOpen_univ : IsOpen (Set.univ : Set ℝ)))
  have outerSmooth : ContDiffAt ℝ ∞ (uncurriedCircle family.tilt)
      (insertion time) :=
    family.tiltSmooth.contDiffAt (domainOpen.mem_nhds insertionIn)
  simpa [Function.comp_def, insertion, uncurriedCircle] using
    outerSmooth.comp time insertionSmooth.contDiffAt

private theorem tilt_order_image_bddAbove
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (order : Fin 3) :
    BddAbove
      ((fun time : ℝ =>
        ‖iteratedFDeriv ℝ order.val
          (family.tilt epsilon parameter.val) time‖) ''
        Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  apply isCompact_Icc.bddAbove_image
  exact ((fixedTilt_contDiff cellLength family epsilon epsilonIn parameter)
    |>.continuous_iteratedFDeriv
      (show (order.val : ℕ∞ω) ≤ ∞ from
        WithTop.coe_le_coe.mpr le_top)).norm.continuousOn

theorem tilt_circleC2_values_bddAbove
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) :
    BddAbove {value : ℝ |
      ∃ (order : Fin 3) (time : ℝ),
        time ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
        value = ‖iteratedFDeriv ℝ order.val
          (family.tilt epsilon parameter.val) time‖} := by
  classical
  choose bound boundUpper using fun order : Fin 3 =>
    tilt_order_image_bddAbove cellLength family epsilon epsilonIn parameter order
  let totalBound : ℝ := ∑ order : Fin 3, max 0 (bound order)
  refine ⟨totalBound, ?_⟩
  rintro value ⟨order, time, timeIn, rfl⟩
  have valueLe :
      ‖iteratedFDeriv ℝ order.val
        (family.tilt epsilon parameter.val) time‖ ≤ bound order :=
    boundUpper order ⟨time, timeIn, rfl⟩
  exact valueLe.trans ((le_max_right 0 (bound order)).trans
    (Finset.single_le_sum (fun index _ => le_max_left 0 (bound index))
      (Finset.mem_univ order)))

theorem tilt_iteratedFDeriv_le_circleC2Seminorm
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (order : Fin 3) (time : ℝ)
    (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖iteratedFDeriv ℝ order.val
      (family.tilt epsilon parameter.val) time‖ ≤
      circleC2Seminorm (family.tilt epsilon parameter.val) := by
  apply le_csSup
    (tilt_circleC2_values_bddAbove cellLength family epsilon epsilonIn parameter)
  exact ⟨order, time, timeIn, rfl⟩

theorem remainder_cellC2Seminorm_nonnegative
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) :
    0 ≤ cellC2Seminorm (family.remainder epsilon parameter.val) := by
  have timeIn : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    exact ⟨le_rfl, (mul_pos (by norm_num) Real.pi_pos).le⟩
  exact (norm_nonneg _).trans
    (remainder_iteratedFDeriv_le_cellC2Seminorm cellLength family epsilon
      epsilonIn parameter 0 0 (by simp) 0 timeIn)

theorem tilt_circleC2Seminorm_nonnegative
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) :
    0 ≤ circleC2Seminorm (family.tilt epsilon parameter.val) := by
  have timeIn : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    exact ⟨le_rfl, (mul_pos (by norm_num) Real.pi_pos).le⟩
  exact (norm_nonneg _).trans
    (tilt_iteratedFDeriv_le_circleC2Seminorm cellLength family epsilon
      epsilonIn parameter 0 0 timeIn)

/-- Every stored Cartesian remainder derivative of order at most two is
controlled by the one uniform physical estimate on the closed disk and one
fundamental cell interval. -/
theorem remainder_iteratedFDeriv_le_physicalBound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (order : Fin 3) (point : Plane) (pointIn : ‖point‖ ≤ 1)
    (time : ℝ) (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖iteratedFDeriv ℝ order.val
      (fun argument : Vec => family.remainder epsilon parameter.val
        (coordinateDisk argument) (argument 1))
      (coordinatePoint point time)‖ ≤ family.bound * |epsilon| := by
  calc
    _ ≤ cellC2Seminorm (family.remainder epsilon parameter.val) :=
      remainder_iteratedFDeriv_le_cellC2Seminorm cellLength family epsilon
        epsilonIn parameter order point pointIn time timeIn
    _ ≤ circleC2Seminorm (family.tilt epsilon parameter.val) +
          cellC2Seminorm (family.remainder epsilon parameter.val) :=
      le_add_of_nonneg_left
        (tilt_circleC2Seminorm_nonnegative cellLength family epsilon epsilonIn
          parameter)
    _ ≤ family.bound * |epsilon| :=
      family.physicalC2Estimate epsilon epsilonIn parameter.val
        parameter.property

/-- Every stored tilt derivative of order at most two is controlled by the
same uniform physical estimate. -/
theorem tilt_iteratedFDeriv_le_physicalBound
    (cellLength : ℝ) (family : CellSolutionFamily cellLength)
    (epsilon : ℝ)
    (epsilonIn : epsilon ∈ Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper)
    (order : Fin 3) (time : ℝ)
    (timeIn : time ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖iteratedFDeriv ℝ order.val
      (family.tilt epsilon parameter.val) time‖ ≤
      family.bound * |epsilon| := by
  calc
    _ ≤ circleC2Seminorm (family.tilt epsilon parameter.val) :=
      tilt_iteratedFDeriv_le_circleC2Seminorm cellLength family epsilon
        epsilonIn parameter order time timeIn
    _ ≤ circleC2Seminorm (family.tilt epsilon parameter.val) +
          cellC2Seminorm (family.remainder epsilon parameter.val) :=
      le_add_of_nonneg_right
        (remainder_cellC2Seminorm_nonnegative cellLength family epsilon
          epsilonIn parameter)
    _ ≤ family.bound * |epsilon| :=
      family.physicalC2Estimate epsilon epsilonIn parameter.val
        parameter.property

end Grad.PhysicalFamily.SampledSeminormBounds
