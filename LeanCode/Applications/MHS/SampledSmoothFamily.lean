import IntegerSampling
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

open Set Filter
open scoped ContDiff

namespace Grad.PhysicalFamily.SampledSmoothFamily

open Grad.MainTarget
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling

/-- Reorder physical cylinder coordinates `(y₁,y₂,φ)` into the cell order
`(y₁,ζ,y₂)`, with the exact integer rescaling `ζ=Nφ`. -/
def resampledCellPoint (period : ℕ) (point : Vec) : Vec :=
  vector (point 0) ((period : ℝ) * point 2) (point 1)

@[simp] theorem coordinateDisk_resampledCellPoint (period : ℕ) (point : Vec) :
    coordinateDisk (resampledCellPoint period point) = planarPart point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [coordinateDisk, resampledCellPoint, planarPart, vector]

@[simp] theorem resampledCellPoint_time (period : ℕ) (point : Vec) :
    resampledCellPoint period point 1 = (period : ℝ) * point 2 := by
  simp [resampledCellPoint, vector]

def sampledCellInput (period : ℕ) (argument : ℝ × Vec) : CellArgument :=
  (sampledEpsilon period, (argument.1, resampledCellPoint period argument.2))

theorem resampledCellPoint_contDiff (period : ℕ) :
    ContDiff ℝ ∞ (resampledCellPoint period) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [resampledCellPoint, vector] <;> fun_prop

theorem sampledCellInput_contDiff (period : ℕ) :
    ContDiff ℝ ∞ (sampledCellInput period) := by
  unfold sampledCellInput
  exact contDiff_const.prodMk
    (contDiff_fst.prodMk
      ((resampledCellPoint_contDiff period).comp contDiff_snd))

@[simp] theorem uncurriedCell_sampledCellInput {Target : Type*}
    (mapping : ℝ → ℝ → Plane → ℝ → Target) (period : ℕ)
    (argument : ℝ × Vec) :
    uncurriedCell mapping (sampledCellInput period argument) =
      mapping (sampledEpsilon period) argument.1 (planarPart argument.2)
        ((period : ℝ) * argument.2 2) := by
  simp [uncurriedCell, sampledCellInput]

/-- The open parameter/collar domain on which the sampled physical lifts use
the stored common smooth cell extension. -/
def sampledPhysicalCollar (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) : Set (ℝ × Vec) :=
  Set.Ioo family.parameterLower family.parameterUpper ×ˢ
    (planarPart ⁻¹' Metric.ball 0 family.collarRadius)

theorem planarPart_contDiff : ContDiff ℝ ∞ planarPart := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [planarPart] <;> fun_prop

theorem sampledPhysicalCollar_isOpen (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    IsOpen (sampledPhysicalCollar cellLength family) := by
  unfold sampledPhysicalCollar
  apply IsOpen.prod isOpen_Ioo
  exact Metric.isOpen_ball.preimage planarPart_contDiff.continuous

theorem sampledCellInput_mem (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    {argument : ℝ × Vec}
    (argumentIn : argument ∈ sampledPhysicalCollar cellLength family) :
    sampledCellInput period argument ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
        (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
          coordinateCollar family.collarRadius) := by
  refine ⟨epsilonIn, argumentIn.1, ?_⟩
  change ‖coordinateDisk (resampledCellPoint period argument.2)‖ <
    family.collarRadius
  rw [coordinateDisk_resampledCellPoint]
  simpa [sampledPhysicalCollar, Metric.mem_ball, dist_zero_right] using
    argumentIn.2

/-- The joint parameter/physical-coordinate evaluation of the sampled cell
solution before applying the ambient rotation. -/
def sampledCellValue (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (argument : ℝ × Vec) : Vec :=
  uncurriedCell family.v (sampledCellInput period argument)

theorem sampledCellValue_contDiffOn (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero) :
    ContDiffOn ℝ ∞ (sampledCellValue cellLength family period)
      (sampledPhysicalCollar cellLength family) := by
  exact family.vSmooth.comp
    (sampledCellInput_contDiff period).contDiffOn
    (fun _ argumentIn =>
      sampledCellInput_mem cellLength family period epsilonIn argumentIn)

def uncurriedRotation (argument : ℝ × Vec) : Vec :=
  rotation argument.1 argument.2

theorem uncurriedRotation_contDiff :
    ContDiff ℝ ∞ uncurriedRotation := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [uncurriedRotation, rotation, vector] <;> fun_prop

theorem physicalTime_contDiff :
    ContDiff ℝ ∞ (fun argument : ℝ × Vec => argument.2 2) := by
  fun_prop

/-- Joint open-collar extension of the exact sampled position lift. -/
def sampledPositionRotationInput (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (argument : ℝ × Vec) : ℝ × Vec :=
  (argument.2 2,
    ((period : ℝ) * cellLength) • basisVector 0 +
      sampledCellValue cellLength family period argument)

theorem sampledPositionRotationInput_contDiffOn (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero) :
    ContDiffOn ℝ ∞
      (sampledPositionRotationInput cellLength family period)
      (sampledPhysicalCollar cellLength family) := by
  exact physicalTime_contDiff.contDiffOn.prodMk
    (contDiffOn_const.add
      (sampledCellValue_contDiffOn cellLength family period epsilonIn))

def sampledPositionJointLift (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (argument : ℝ × Vec) : Vec :=
  (uncurriedRotation ∘
    sampledPositionRotationInput cellLength family period) argument

theorem sampledPositionJointLift_eq (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (argument : ℝ × Vec) :
    sampledPositionJointLift cellLength family period argument =
      sampledPositionLift cellLength family period argument.1
        (planarPart argument.2) (argument.2 2) := by
  simp [sampledPositionJointLift, sampledPositionRotationInput,
    uncurriedRotation, sampledPositionLift, sampledCellValue]

theorem sampledPositionJointLift_contDiffOn (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero) :
    ContDiffOn ℝ ∞ (sampledPositionJointLift cellLength family period)
      (sampledPhysicalCollar cellLength family) := by
  exact uncurriedRotation_contDiff.contDiffOn.comp
    (sampledPositionRotationInput_contDiffOn cellLength family period epsilonIn)
    (mapsTo_univ _ _)

/-- Joint open-collar extension of the sampled pressure lift. -/
def sampledPressureJointLift (potential : ℝ) (argument : ℝ × Vec) : ℝ :=
  potential - ‖planarPart argument.2‖ ^ 2

theorem sampledPressureJointLift_eq (potential : ℝ) (argument : ℝ × Vec) :
    sampledPressureJointLift potential argument =
      sampledPressureLift potential (planarPart argument.2) (argument.2 2) := by
  rfl

theorem sampledPressureJointLift_contDiff (potential : ℝ) :
    ContDiff ℝ ∞ (sampledPressureJointLift potential) := by
  unfold sampledPressureJointLift
  exact contDiff_const.sub
    ((contDiff_norm_sq ℝ).comp (planarPart_contDiff.comp contDiff_snd))

theorem coordinateDisk_contDiff : ContDiff ℝ ∞ coordinateDisk := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [coordinateDisk] <;> fun_prop

theorem coordinateCollar_isOpen (radius : ℝ) :
    IsOpen (coordinateCollar radius) := by
  have equality : coordinateCollar radius =
      coordinateDisk ⁻¹' Metric.ball 0 radius := by
    ext point
    simp [coordinateCollar, Metric.mem_ball, dist_zero_right]
  rw [equality]
  exact Metric.isOpen_ball.preimage coordinateDisk_contDiff.continuous

def cellSmoothDomain (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) : Set CellArgument :=
  Set.Ioo (-family.epsilonZero) family.epsilonZero ×ˢ
    (Set.Ioo family.parameterLower family.parameterUpper ×ˢ
      coordinateCollar family.collarRadius)

theorem cellSmoothDomain_isOpen (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    IsOpen (cellSmoothDomain cellLength family) := by
  exact isOpen_Ioo.prod (isOpen_Ioo.prod
    (coordinateCollar_isOpen family.collarRadius))

theorem fullCellDerivative_contDiffOn (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    ContDiffOn ℝ ∞ (fderiv ℝ (uncurriedCell family.v))
      (cellSmoothDomain cellLength family) := by
  exact family.vSmooth.fderiv_of_isOpen
    (cellSmoothDomain_isOpen cellLength family) (by simp)

theorem coordinatePoint_uncurried_contDiff :
    ContDiff ℝ ∞ (fun argument : Plane × ℝ =>
      coordinatePoint argument.1 argument.2) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [coordinatePoint, vector] <;> fun_prop

@[simp] theorem coordinateDisk_coordinatePoint (point : Plane) (time : ℝ) :
    coordinateDisk (coordinatePoint point time) = point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [coordinateDisk, coordinatePoint, vector]

@[simp] theorem coordinatePoint_time (point : Plane) (time : ℝ) :
    coordinatePoint point time 1 = time := by
  simp [coordinatePoint, vector]

theorem planeQuarterTurn_contDiff : ContDiff ℝ ∞ planeQuarterTurn := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [planeQuarterTurn] <;> fun_prop

/-- For fixed physical parameter/time data, insert a variable disk point into
the exact cell argument. -/
def sampledDiskSection (period : ℕ) (argument : ℝ × Vec)
    (point : Plane) : CellArgument :=
  (sampledEpsilon period,
    (argument.1, coordinatePoint point ((period : ℝ) * argument.2 2)))

theorem sampledDiskSection_uncurry_contDiff (period : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (sampledDiskSection period)) := by
  have cellPointSmooth : ContDiff ℝ ∞
      (fun argument : (ℝ × Vec) × Plane =>
        coordinatePoint argument.2
          ((period : ℝ) * argument.1.2 2)) :=
    coordinatePoint_uncurried_contDiff.comp
      (contDiff_snd.prodMk (by fun_prop))
  exact contDiff_const.prodMk (contDiff_fst.fst.prodMk cellPointSmooth)

theorem sampledDiskSection_contDiff (period : ℕ) (argument : ℝ × Vec) :
    ContDiff ℝ ∞ (sampledDiskSection period argument) :=
  (sampledDiskSection_uncurry_contDiff period).comp
    (contDiff_const.prodMk contDiff_id)

@[simp] theorem sampledDiskSection_planarPart (period : ℕ)
    (argument : ℝ × Vec) :
    sampledDiskSection period argument (planarPart argument.2) =
      sampledCellInput period argument := by
  simp [sampledDiskSection, sampledCellInput, resampledCellPoint,
    coordinatePoint, planarPart, vector]

/-- The exact full-cell tangent direction corresponding to the disk angular
direction after freezing epsilon, parameter, and resampled cell time. -/
def sampledDiskDirection (period : ℕ) (argument : ℝ × Vec) : CellArgument :=
  fderiv ℝ (sampledDiskSection period argument) (planarPart argument.2)
    (planeQuarterTurn (planarPart argument.2))

theorem sampledDiskDirection_contDiff (period : ℕ) :
    ContDiff ℝ ∞ (sampledDiskDirection period) := by
  exact (sampledDiskSection_uncurry_contDiff period).fderiv_apply
    (planarPart_contDiff.comp contDiff_snd)
    (planeQuarterTurn_contDiff.comp
      (planarPart_contDiff.comp contDiff_snd)) (by simp)

/-- Disk-angular differentiation expressed as evaluation of the full smooth
cell derivative at the sampled input and its exact inserted tangent. -/
def sampledCellAngularValue (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (argument : ℝ × Vec) : Vec :=
  fderiv ℝ (uncurriedCell family.v) (sampledCellInput period argument)
    (sampledDiskDirection period argument)

theorem sampledCellAngularValue_contDiffOn (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero) :
    ContDiffOn ℝ ∞ (sampledCellAngularValue cellLength family period)
      (sampledPhysicalCollar cellLength family) := by
  have derivativeSmooth : ContDiffOn ℝ ∞
      (fun argument : ℝ × Vec =>
        fderiv ℝ (uncurriedCell family.v) (sampledCellInput period argument))
      (sampledPhysicalCollar cellLength family) :=
    (fullCellDerivative_contDiffOn cellLength family).comp
      (sampledCellInput_contDiff period).contDiffOn
      (fun _ argumentIn =>
        sampledCellInput_mem cellLength family period epsilonIn argumentIn)
  exact derivativeSmooth.clm_apply
    (sampledDiskDirection_contDiff period).contDiffOn

theorem sampledCellAngularValue_eq_diskAngular (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (argument : ℝ × Vec)
    (argumentIn : argument ∈ sampledPhysicalCollar cellLength family) :
    sampledCellAngularValue cellLength family period argument =
      diskAngular (family.v (sampledEpsilon period) argument.1)
        (planarPart argument.2) ((period : ℝ) * argument.2 2) := by
  have inputIn : sampledCellInput period argument ∈
      cellSmoothDomain cellLength family := by
    simpa [cellSmoothDomain] using
      sampledCellInput_mem cellLength family period epsilonIn argumentIn
  have outerSmooth : ContDiffOn ℝ ∞ (uncurriedCell family.v)
      (cellSmoothDomain cellLength family) := by
    simpa [cellSmoothDomain] using family.vSmooth
  have outerDifferentiable : DifferentiableAt ℝ (uncurriedCell family.v)
      (sampledCellInput period argument) :=
    (outerSmooth.contDiffAt
      ((cellSmoothDomain_isOpen cellLength family).mem_nhds inputIn)).differentiableAt
      (by simp)
  have innerDifferentiable : DifferentiableAt ℝ
      (sampledDiskSection period argument) (planarPart argument.2) :=
    (ContDiff.differentiable
      (sampledDiskSection_contDiff period argument) (by simp)).differentiableAt
  let direction := planeQuarterTurn (planarPart argument.2)
  have chainRule := fderiv_comp
    (x := planarPart argument.2) outerDifferentiable innerDifferentiable
  have evaluated := congrArg
    (fun derivative : Plane →L[ℝ] Vec => derivative direction) chainRule
  calc
    sampledCellAngularValue cellLength family period argument =
        fderiv ℝ (uncurriedCell family.v)
          (sampledDiskSection period argument (planarPart argument.2))
          (fderiv ℝ (sampledDiskSection period argument)
            (planarPart argument.2) direction) := by
              simp [sampledCellAngularValue, sampledDiskDirection, direction]
    _ = fderiv ℝ
          (uncurriedCell family.v ∘ sampledDiskSection period argument)
          (planarPart argument.2) direction := by
            simpa using evaluated.symm
    _ = diskAngular (family.v (sampledEpsilon period) argument.1)
          (planarPart argument.2) ((period : ℝ) * argument.2 2) := by
            unfold diskAngular
            congr 2
            funext point
            simp [uncurriedCell, sampledDiskSection]

def sampledMagneticRotationInput (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (argument : ℝ × Vec) : ℝ × Vec :=
  (argument.2 2, sampledCellAngularValue cellLength family period argument)

theorem sampledMagneticRotationInput_contDiffOn (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero) :
    ContDiffOn ℝ ∞
      (sampledMagneticRotationInput cellLength family period)
      (sampledPhysicalCollar cellLength family) := by
  exact physicalTime_contDiff.contDiffOn.prodMk
    (sampledCellAngularValue_contDiffOn cellLength family period epsilonIn)

/-- Joint open-collar extension of the exact sampled magnetic lift. -/
def sampledMagneticJointLift (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (argument : ℝ × Vec) : Vec :=
  (uncurriedRotation ∘
    sampledMagneticRotationInput cellLength family period) argument

theorem sampledMagneticJointLift_contDiffOn (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero) :
    ContDiffOn ℝ ∞ (sampledMagneticJointLift cellLength family period)
      (sampledPhysicalCollar cellLength family) := by
  exact uncurriedRotation_contDiff.contDiffOn.comp
    (sampledMagneticRotationInput_contDiffOn
      cellLength family period epsilonIn) (mapsTo_univ _ _)

theorem sampledMagneticJointLift_eq (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (argument : ℝ × Vec)
    (argumentIn : argument ∈ sampledPhysicalCollar cellLength family) :
    sampledMagneticJointLift cellLength family period argument =
      sampledMagneticLift cellLength family period argument.1
        (planarPart argument.2) (argument.2 2) := by
  rw [sampledMagneticLift]
  simp only [sampledMagneticJointLift, Function.comp_apply,
    sampledMagneticRotationInput, uncurriedRotation]
  rw [sampledCellAngularValue_eq_diskAngular
    cellLength family period epsilonIn argument argumentIn]

theorem sampledPosition_periodic_open (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : ℝ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    sampledPositionLift cellLength family period parameter point
        (time + 2 * Real.pi) =
      sampledPositionLift cellLength family period parameter point time := by
  have pointInCollar := closed_disk_mem_collar cellLength family point pointIn
  unfold sampledPositionLift
  rw [rotation_add_two_pi]
  rw [show (period : ℝ) * (time + 2 * Real.pi) =
      (period : ℝ) * time + 2 * Real.pi * period by ring]
  rw [periodic_nat_mul
    (family.v (sampledEpsilon period) parameter point)
    (family.vPeriodic (sampledEpsilon period) epsilonIn parameter
      parameterIn point pointInCollar) period ((period : ℝ) * time)]

theorem sampledMagnetic_periodic_open (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : ℝ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (point : Plane) (pointIn : ‖point‖ ≤ 1) (time : ℝ) :
    sampledMagneticLift cellLength family period parameter point
        (time + 2 * Real.pi) =
      sampledMagneticLift cellLength family period parameter point time := by
  have pointInCollar := closed_disk_mem_collar cellLength family point pointIn
  unfold sampledMagneticLift
  rw [rotation_add_two_pi]
  rw [show (period : ℝ) * (time + 2 * Real.pi) =
      (period : ℝ) * time + 2 * Real.pi * period by ring]
  rw [diskAngular_periodic_nat cellLength family (sampledEpsilon period)
    parameter epsilonIn parameterIn point pointInCollar period
    ((period : ℝ) * time)]

theorem sampledPosition_isPeriodic_open (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : ℝ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (point : ClosedDisk) :
    Function.Periodic
      (sampledPositionLift cellLength family period parameter point.val)
      (2 * Real.pi) :=
  sampledPosition_periodic_open cellLength family period parameter epsilonIn
    parameterIn point.val point.property

theorem sampledMagnetic_isPeriodic_open (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (parameter : ℝ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (point : ClosedDisk) :
    Function.Periodic
      (sampledMagneticLift cellLength family period parameter point.val)
      (2 * Real.pi) :=
  sampledMagnetic_periodic_open cellLength family period parameter epsilonIn
    parameterIn point.val point.property

/-- The sampled representative at every parameter of the stored open
parameter neighborhood. -/
def sampledRepresentativeOpen (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (potential : ℝ) : Representative where
  position reference :=
    (sampledPosition_isPeriodic_open cellLength family period parameter
      epsilonIn parameterIn reference.1).lift reference.2
  magnetic reference :=
    (sampledMagnetic_isPeriodic_open cellLength family period parameter
      epsilonIn parameterIn reference.1).lift reference.2
  pressure reference :=
    (sampledPressure_isPeriodic potential reference.1).lift reference.2

@[simp] theorem sampledRepresentativeOpen_position_coe (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (potential : ℝ) (point : ClosedDisk) (time : ℝ) :
    (sampledRepresentativeOpen cellLength family period epsilonIn parameter
      parameterIn potential).position (point, (time : CellCircle)) =
      sampledPositionLift cellLength family period parameter point.val time :=
  rfl

@[simp] theorem sampledRepresentativeOpen_magnetic_coe (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (potential : ℝ) (point : ClosedDisk) (time : ℝ) :
    (sampledRepresentativeOpen cellLength family period epsilonIn parameter
      parameterIn potential).magnetic (point, (time : CellCircle)) =
      sampledMagneticLift cellLength family period parameter point.val time :=
  rfl

@[simp] theorem sampledRepresentativeOpen_pressure_coe (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (potential : ℝ) (point : ClosedDisk) (time : ℝ) :
    (sampledRepresentativeOpen cellLength family period epsilonIn parameter
      parameterIn potential).pressure (point, (time : CellCircle)) =
      sampledPressureLift potential point.val time :=
  rfl

theorem periodicLift_sampledRepresentativeOpen_position (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (potential : ℝ) (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentativeOpen cellLength family period epsilonIn
          parameter parameterIn potential).position point =
      sampledPositionLift cellLength family period parameter
        (planarPart point) (point 2) := by
  simp [periodicLift, pointIn, quotientPoint]

theorem periodicLift_sampledRepresentativeOpen_magnetic (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (potential : ℝ) (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentativeOpen cellLength family period epsilonIn
          parameter parameterIn potential).magnetic point =
      sampledMagneticLift cellLength family period parameter
        (planarPart point) (point 2) := by
  simp [periodicLift, pointIn, quotientPoint]

theorem periodicLift_sampledRepresentativeOpen_pressure (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (potential : ℝ) (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentativeOpen cellLength family period epsilonIn
          parameter parameterIn potential).pressure point =
      sampledPressureLift potential (planarPart point) (point 2) := by
  simp [periodicLift, pointIn, quotientPoint]

def lowerClosedParameter (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    Set.Icc family.lower family.upper :=
  ⟨family.lower, le_rfl, family.intervalNontrivial.le⟩

/-- A total representative-valued parameter extension.  On the stored open
parameter neighborhood it is the exact sampled formula; the fallback is used
only outside that neighborhood. -/
def sampledRepresentativeExtension (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : ℝ) : Representative := by
  classical
  exact if parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper then
    sampledRepresentativeOpen cellLength family period epsilonIn parameter
      parameterIn potential
  else
    sampledRepresentative cellLength family period
      (lowerClosedParameter cellLength family) epsilonIn potential

def sampledRepresentativeFamily (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) :
    Set.Icc family.lower family.upper → Representative :=
  fun parameter => sampledRepresentativeExtension cellLength family period
    epsilonIn potential parameter.val

theorem closedInterval_subset_parameterNeighborhood (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    Set.Icc family.lower family.upper ⊆
      Set.Ioo family.parameterLower family.parameterUpper := by
  intro parameter parameterIn
  exact ⟨lt_of_lt_of_le family.parameterContains.1 parameterIn.1,
    lt_of_le_of_lt parameterIn.2 family.parameterContains.2⟩

theorem parameterCylinder_subset_sampledPhysicalCollar (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) :
    Set.Ioo family.parameterLower family.parameterUpper ×ˢ cylinder ⊆
      sampledPhysicalCollar cellLength family := by
  intro argument argumentIn
  refine ⟨argumentIn.1, ?_⟩
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
  exact lt_of_le_of_lt argumentIn.2 family.collarLarge

theorem periodicLift_sampledRepresentativeExtension_position (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentativeExtension cellLength family period epsilonIn
          potential parameter).position point =
      sampledPositionLift cellLength family period parameter
        (planarPart point) (point 2) := by
  simp [sampledRepresentativeExtension, parameterIn,
    periodicLift_sampledRepresentativeOpen_position, pointIn]

theorem periodicLift_sampledRepresentativeExtension_magnetic (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentativeExtension cellLength family period epsilonIn
          potential parameter).magnetic point =
      sampledMagneticLift cellLength family period parameter
        (planarPart point) (point 2) := by
  simp [sampledRepresentativeExtension, parameterIn,
    periodicLift_sampledRepresentativeOpen_magnetic, pointIn]

theorem periodicLift_sampledRepresentativeExtension_pressure (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential parameter : ℝ)
    (parameterIn : parameter ∈
      Set.Ioo family.parameterLower family.parameterUpper)
    (point : Vec) (pointIn : point ∈ cylinder) :
    periodicLift
        (sampledRepresentativeExtension cellLength family period epsilonIn
          potential parameter).pressure point =
      sampledPressureLift potential (planarPart point) (point 2) := by
  simp [sampledRepresentativeExtension, parameterIn,
    periodicLift_sampledRepresentativeOpen_pressure, pointIn]

theorem sampledPosition_hasLocalExtensions (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) :
    HasLocalExtensions .smooth
      (fun argument : ℝ × Vec =>
        periodicLift
          (sampledRepresentativeExtension cellLength family period epsilonIn
            potential argument.1).position argument.2)
      (Set.Ioo family.parameterLower family.parameterUpper ×ˢ cylinder) := by
  intro argument argumentIn
  refine ⟨sampledPhysicalCollar cellLength family,
    sampledPhysicalCollar_isOpen cellLength family,
    parameterCylinder_subset_sampledPhysicalCollar cellLength family argumentIn,
    sampledPositionJointLift cellLength family period,
    sampledPositionJointLift_contDiffOn cellLength family period epsilonIn, ?_⟩
  intro point pointIn
  rw [sampledPositionJointLift_eq]
  symm
  exact periodicLift_sampledRepresentativeExtension_position
    cellLength family period epsilonIn potential point.1 pointIn.2.1
      point.2 pointIn.2.2

theorem sampledMagnetic_hasLocalExtensions (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) :
    HasLocalExtensions .smooth
      (fun argument : ℝ × Vec =>
        periodicLift
          (sampledRepresentativeExtension cellLength family period epsilonIn
            potential argument.1).magnetic argument.2)
      (Set.Ioo family.parameterLower family.parameterUpper ×ˢ cylinder) := by
  intro argument argumentIn
  refine ⟨sampledPhysicalCollar cellLength family,
    sampledPhysicalCollar_isOpen cellLength family,
    parameterCylinder_subset_sampledPhysicalCollar cellLength family argumentIn,
    sampledMagneticJointLift cellLength family period,
    sampledMagneticJointLift_contDiffOn cellLength family period epsilonIn, ?_⟩
  intro point pointIn
  rw [sampledMagneticJointLift_eq cellLength family period epsilonIn point
    pointIn.1]
  symm
  exact periodicLift_sampledRepresentativeExtension_magnetic
    cellLength family period epsilonIn potential point.1 pointIn.2.1
      point.2 pointIn.2.2

theorem sampledPressure_hasLocalExtensions (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) :
    HasLocalExtensions .smooth
      (fun argument : ℝ × Vec =>
        periodicLift
          (sampledRepresentativeExtension cellLength family period epsilonIn
            potential argument.1).pressure argument.2)
      (Set.Ioo family.parameterLower family.parameterUpper ×ˢ cylinder) := by
  intro argument argumentIn
  refine ⟨sampledPhysicalCollar cellLength family,
    sampledPhysicalCollar_isOpen cellLength family,
    parameterCylinder_subset_sampledPhysicalCollar cellLength family argumentIn,
    sampledPressureJointLift potential,
    (sampledPressureJointLift_contDiff potential).contDiffOn, ?_⟩
  intro point pointIn
  rw [sampledPressureJointLift_eq]
  symm
  exact periodicLift_sampledRepresentativeExtension_pressure
    cellLength family period epsilonIn potential point.1 pointIn.2.1
      point.2 pointIn.2.2

/-- Exact target-level parameter smoothness for the sampled representatives,
using one common open parameter neighborhood and the literal sampled maps. -/
theorem sampled_smoothRepresentatives (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) :
    SmoothRepresentatives (Set.Icc family.lower family.upper)
      (sampledRepresentativeFamily cellLength family period epsilonIn
        potential) := by
  refine ⟨Set.Ioo family.parameterLower family.parameterUpper, isOpen_Ioo,
    closedInterval_subset_parameterNeighborhood cellLength family,
    sampledRepresentativeExtension cellLength family period epsilonIn
      potential, ?_, ?_, ?_, ?_⟩
  · intro parameter
    rfl
  · exact sampledPosition_hasLocalExtensions
      cellLength family period epsilonIn potential
  · exact sampledMagnetic_hasLocalExtensions
      cellLength family period epsilonIn potential
  · exact sampledPressure_hasLocalExtensions
      cellLength family period epsilonIn potential

end Grad.PhysicalFamily.SampledSmoothFamily
