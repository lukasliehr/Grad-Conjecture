import PhysicalNormalHessianConsumer
import SampledSmoothFamily
import SampledPhysicalSimilarityRigidity

noncomputable section

open Set
open scoped ContDiff

namespace Grad.MainAssembly.SampledAxisBasics

open Grad.MainTarget
open Grad.MainAssembly.CircleIsometryClassification
open Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.SampledPhysicalSimilarityRigidity
open Grad.MainAssembly.PhysicalNormalHessian

noncomputable def cellAxisLinearMap (rho alpha delta parameter time a : ℝ)
    (tilt : Plane) : Plane →ₗ[ℝ] Vec where
  toFun point :=
    a • planeEmbedding (seedAction rho alpha delta parameter time point) +
      planeDot tilt point • tangentDirection
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;>
      simp [seedAction, planeEmbedding, planeDot, tangentDirection,
        basisVector, vector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;>
      simp [seedAction, planeEmbedding, planeDot, tangentDirection,
        basisVector, vector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> ring

noncomputable def cellAxisCLM (rho alpha delta parameter time a : ℝ)
    (tilt : Plane) : Plane →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap
    (cellAxisLinearMap rho alpha delta parameter time a tilt)

@[simp] theorem cellAxisCLM_apply (rho alpha delta parameter time a : ℝ)
    (tilt point : Plane) :
    cellAxisCLM rho alpha delta parameter time a tilt point =
      a • planeEmbedding (seedAction rho alpha delta parameter time point) +
        planeDot tilt point • tangentDirection :=
  rfl

noncomputable def physicalDiskLinearMap : Plane →ₗ[ℝ] Vec where
  toFun disk := coordinateDirection disk 0
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [coordinateDirection, vector]
  map_smul' scalar disk := by
    ext coordinate
    fin_cases coordinate <;> simp [coordinateDirection, vector]

noncomputable def physicalDiskCLM : Plane →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap physicalDiskLinearMap

@[simp] theorem physicalDiskCLM_apply (disk : Plane) :
    physicalDiskCLM disk = coordinateDirection disk 0 :=
  rfl

noncomputable def physicalToroidalLinearMap : ℝ →ₗ[ℝ] Vec where
  toFun toroidal := coordinateDirection 0 toroidal
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [coordinateDirection, vector]
  map_smul' scalar toroidal := by
    ext coordinate
    fin_cases coordinate <;> simp [coordinateDirection, vector]

noncomputable def physicalToroidalCLM : ℝ →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap physicalToroidalLinearMap

@[simp] theorem physicalToroidalCLM_apply (toroidal : ℝ) :
    physicalToroidalCLM toroidal = coordinateDirection 0 toroidal :=
  rfl

def sampledCellCoordinateValue (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ) (parameter : ℝ)
    (point : Vec) : Vec :=
  sampledCellValue cellLength family period (parameter, point)

theorem sampledCellCoordinateValue_differentiableAt_axis (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    DifferentiableAt ℝ
      (sampledCellCoordinateValue cellLength family period parameter.val)
      (vector 0 0 time) := by
  let argument : ℝ × Vec := (parameter.val, vector 0 0 time)
  have argumentIn : argument ∈ sampledPhysicalCollar cellLength family := by
    refine ⟨parameter_mem_open cellLength family parameter, ?_⟩
    change planarPart (vector 0 0 time) ∈ Metric.ball 0 family.collarRadius
    have planarZero : planarPart (vector 0 0 time) = 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [planarPart, vector]
    rw [Metric.mem_ball, dist_zero_right, planarZero, norm_zero]
    linarith [family.collarLarge]
  have jointDifferentiable : DifferentiableAt ℝ
      (sampledCellValue cellLength family period) argument :=
    ((sampledCellValue_contDiffOn cellLength family period epsilonIn).contDiffAt
      ((sampledPhysicalCollar_isOpen cellLength family).mem_nhds
        argumentIn)).differentiableAt (by simp)
  have insertionDifferentiable : DifferentiableAt ℝ
      (fun point : Vec => (parameter.val, point)) (vector 0 0 time) := by
    fun_prop
  have composed := jointDifferentiable.comp (vector 0 0 time)
    insertionDifferentiable
  change DifferentiableAt ℝ
    (fun point : Vec =>
      sampledCellValue cellLength family period (parameter.val, point))
    (vector 0 0 time)
  simpa [Function.comp_def, argument] using composed

theorem normalizedFactor_positive (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    0 < normalizedFactor
      (family.tilt (sampledEpsilon period) parameter.val time) := by
  apply Real.sqrt_pos.mpr
  have tiltBound := family.tiltBound (sampledEpsilon period) epsilonIn
    parameter.val parameter.property time
  nlinarith

theorem cell_disk_fderiv_axis (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    fderiv ℝ
        (fun point : Plane =>
          family.v (sampledEpsilon period) parameter.val point
            ((period : ℝ) * time)) 0 =
      cellAxisCLM family.rho family.alpha family.delta parameter.val
        ((period : ℝ) * time)
        (normalizedFactor
          (family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time)))
        (family.tilt (sampledEpsilon period) parameter.val
          ((period : ℝ) * time)) := by
  let cellTime := (period : ℝ) * time
  let a := normalizedFactor
    (family.tilt (sampledEpsilon period) parameter.val cellTime)
  let tilt := family.tilt (sampledEpsilon period) parameter.val cellTime
  have localEquality :
      (fun point : Plane =>
        family.v (sampledEpsilon period) parameter.val point cellTime) =ᶠ[nhds 0]
      (fun point : Plane =>
        cellAxisCLM family.rho family.alpha family.delta parameter.val cellTime
            a tilt point +
          family.remainder (sampledEpsilon period) parameter.val point
            cellTime) := by
    have ballNeighborhood : Metric.ball (0 : Plane) 1 ∈ nhds 0 :=
      Metric.isOpen_ball.mem_nhds (by simp)
    filter_upwards [ballNeighborhood] with point pointIn
    rw [family.normalizedChart (sampledEpsilon period) epsilonIn
      parameter.val parameter.property point]
    · rfl
    · exact le_of_lt (by
        simpa [Metric.mem_ball, dist_zero_right] using pointIn)
  have remainderDifferentiable : DifferentiableAt ℝ
      (fun point : Plane =>
        family.remainder (sampledEpsilon period) parameter.val point cellTime) 0 := by
    let diskSection : Plane → CellArgument := fun point =>
      (sampledEpsilon period,
        (parameter.val, coordinatePoint point cellTime))
    have inputIn : diskSection 0 ∈ cellSmoothDomain cellLength family := by
      refine ⟨epsilonIn, parameter_mem_open cellLength family parameter, ?_⟩
      change coordinatePoint (0 : Plane) cellTime ∈
        coordinateCollar family.collarRadius
      change ‖coordinateDisk (coordinatePoint (0 : Plane) cellTime)‖ <
        family.collarRadius
      rw [coordinateDisk_coordinatePoint, norm_zero]
      linarith [family.collarLarge]
    have outerDifferentiable : DifferentiableAt ℝ
        (uncurriedCell family.remainder) (diskSection 0) :=
      (family.remainderSmooth.contDiffAt
        ((cellSmoothDomain_isOpen cellLength family).mem_nhds
          (by simpa [cellSmoothDomain] using inputIn))).differentiableAt
        (by simp)
    have sectionDifferentiable : DifferentiableAt ℝ
        diskSection 0 := by
      have coordinatePointSmooth : ContDiff ℝ ∞
          (fun point : Plane => coordinatePoint point cellTime) := by
        have timeSmooth : ContDiff ℝ ∞ (fun _ : Plane => cellTime) :=
          contDiff_const
        simpa [Function.comp_def] using
          coordinatePoint_uncurried_contDiff.comp
            (contDiff_id.prodMk timeSmooth)
      have diskSectionSmooth : ContDiff ℝ ∞ diskSection := by
        dsimp [diskSection]
        exact contDiff_const.prodMk
          (contDiff_const.prodMk coordinatePointSmooth)
      exact (diskSectionSmooth.differentiable (by simp)).differentiableAt
    have composed := outerDifferentiable.comp 0 sectionDifferentiable
    simpa [Function.comp_def, uncurriedCell, diskSection] using composed
  rw [localEquality.fderiv_eq]
  have sumDerivative := fderiv_add
    (cellAxisCLM family.rho family.alpha family.delta parameter.val cellTime
      a tilt).differentiableAt remainderDifferentiable
  change fderiv ℝ
      (fun point : Plane =>
        cellAxisCLM family.rho family.alpha family.delta parameter.val
            cellTime a tilt point +
          family.remainder (sampledEpsilon period) parameter.val point cellTime)
      0 =
    fderiv ℝ (cellAxisCLM family.rho family.alpha family.delta parameter.val
      cellTime a tilt) 0 +
    fderiv ℝ (fun point : Plane =>
      family.remainder (sampledEpsilon period) parameter.val point cellTime) 0
      at sumDerivative
  rw [sumDerivative]
  rw [(cellAxisCLM family.rho family.alpha family.delta parameter.val
    cellTime a tilt).fderiv]
  rw [family.remainderDerivativeZero (sampledEpsilon period) epsilonIn
    parameter.val parameter.property cellTime]
  simp [cellTime, a, tilt]

theorem sampledCellCoordinateValue_fderiv_disk (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ)
    (disk : Plane) :
    fderiv ℝ
        (sampledCellCoordinateValue cellLength family period parameter.val)
        (vector 0 0 time) (coordinateDirection disk 0) =
      cellAxisCLM family.rho family.alpha family.delta parameter.val
        ((period : ℝ) * time)
        (normalizedFactor
          (family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time)))
        (family.tilt (sampledEpsilon period) parameter.val
          ((period : ℝ) * time)) disk := by
  let coordinateBase : Vec := vector 0 0 time
  let diskInsertion : Plane → Vec :=
    (fun _ : Plane => coordinateBase) + physicalDiskCLM
  have insertionHasDerivative : HasFDerivAt diskInsertion physicalDiskCLM 0 := by
    simpa only [Pi.add_apply, zero_add] using
      (hasFDerivAt_const (x := (0 : Plane)) coordinateBase).add
        physicalDiskCLM.hasFDerivAt
  have insertionZero : diskInsertion 0 = vector 0 0 time := by
    simp [diskInsertion, coordinateBase, physicalDiskCLM_apply,
      coordinateDirection, vector]
  have cellDifferentiable :=
    sampledCellCoordinateValue_differentiableAt_axis cellLength family period
      epsilonIn parameter time
  have cellDifferentiableAtInsertion : DifferentiableAt ℝ
      (sampledCellCoordinateValue cellLength family period parameter.val)
      (diskInsertion 0) := by
    rw [insertionZero]
    exact cellDifferentiable
  have chainRule := fderiv_comp (x := (0 : Plane))
    cellDifferentiableAtInsertion
    insertionHasDerivative.differentiableAt
  rw [insertionZero] at chainRule
  rw [insertionHasDerivative.fderiv] at chainRule
  have compositionEquality :
      sampledCellCoordinateValue cellLength family period parameter.val ∘
          diskInsertion =
        fun point : Plane =>
          family.v (sampledEpsilon period) parameter.val point
            ((period : ℝ) * time) := by
    funext point
    change family.v (sampledEpsilon period) parameter.val
        (planarPart (diskInsertion point))
        ((period : ℝ) * (diskInsertion point) 2) =
      family.v (sampledEpsilon period) parameter.val point
        ((period : ℝ) * time)
    have planarIdentity : planarPart (diskInsertion point) = point := by
      ext coordinate
      fin_cases coordinate <;>
        simp [diskInsertion, coordinateBase, physicalDiskCLM_apply,
          coordinateDirection, planarPart, vector]
    have timeIdentity : (diskInsertion point) 2 = time := by
      simp [diskInsertion, coordinateBase, physicalDiskCLM_apply,
        coordinateDirection, vector]
    rw [planarIdentity, timeIdentity]
  rw [compositionEquality,
    cell_disk_fderiv_axis cellLength family period epsilonIn parameter time]
    at chainRule
  have evaluated := congrArg (fun derivative : Plane →L[ℝ] Vec =>
    derivative disk) chainRule
  simpa using evaluated.symm

theorem cell_value_axis_zero (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    family.v (sampledEpsilon period) parameter.val 0 time = 0 := by
  have seedZero :
      seedAction family.rho family.alpha family.delta parameter.val time 0 = 0 := by
    ext coordinate
    change
      Matrix.mulVec
        (Grad.GeometryClosure.harmonicSeedMatrix family.rho family.alpha
          family.delta parameter.val time) (0 : Fin 2 → ℝ) coordinate = 0
    rw [Matrix.mulVec_zero]
    rfl
  have embedZero : planeEmbedding (0 : Plane) = 0 := by
    ext coordinate
    fin_cases coordinate <;> simp [planeEmbedding, vector]
  rw [family.normalizedChart (sampledEpsilon period) epsilonIn parameter.val
    parameter.property 0 (by simp) time]
  rw [family.remainderValueZero (sampledEpsilon period) epsilonIn
    parameter.val parameter.property time]
  rw [seedZero]
  rw [embedZero]
  simp [planeDot]

theorem sampledCellCoordinateValue_fderiv_toroidal (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time toroidal : ℝ) :
    fderiv ℝ
        (sampledCellCoordinateValue cellLength family period parameter.val)
        (vector 0 0 time) (coordinateDirection 0 toroidal) = 0 := by
  let coordinateBase : Vec := vector 0 0 time
  let toroidalInsertion : ℝ → Vec :=
    (fun _ : ℝ => coordinateBase) + physicalToroidalCLM
  have insertionHasDerivative :
      HasFDerivAt toroidalInsertion physicalToroidalCLM 0 := by
    simpa only [Pi.add_apply, zero_add] using
      (hasFDerivAt_const (x := (0 : ℝ)) coordinateBase).add
        physicalToroidalCLM.hasFDerivAt
  have insertionZero : toroidalInsertion 0 = vector 0 0 time := by
    simp [toroidalInsertion, coordinateBase, physicalToroidalCLM_apply,
      coordinateDirection, vector]
  have cellDifferentiable :=
    sampledCellCoordinateValue_differentiableAt_axis cellLength family period
      epsilonIn parameter time
  have cellDifferentiableAtInsertion : DifferentiableAt ℝ
      (sampledCellCoordinateValue cellLength family period parameter.val)
      (toroidalInsertion 0) := by
    rw [insertionZero]
    exact cellDifferentiable
  have chainRule := fderiv_comp (x := (0 : ℝ))
    cellDifferentiableAtInsertion insertionHasDerivative.differentiableAt
  rw [insertionZero, insertionHasDerivative.fderiv] at chainRule
  have compositionEquality :
      sampledCellCoordinateValue cellLength family period parameter.val ∘
          toroidalInsertion =
        fun _ : ℝ => (0 : Vec) := by
    funext offset
    change family.v (sampledEpsilon period) parameter.val
        (planarPart (toroidalInsertion offset))
        ((period : ℝ) * (toroidalInsertion offset) 2) = 0
    have planarIdentity : planarPart (toroidalInsertion offset) = 0 := by
      ext coordinate
      fin_cases coordinate <;>
        simp [toroidalInsertion, coordinateBase, physicalToroidalCLM_apply,
          coordinateDirection, planarPart, vector]
    rw [planarIdentity]
    exact cell_value_axis_zero cellLength family period epsilonIn parameter _
  rw [compositionEquality] at chainRule
  have evaluated := congrArg (fun derivative : ℝ →L[ℝ] Vec =>
    derivative toroidal) chainRule
  simpa using evaluated.symm

theorem coordinateDirection_add (disk : Plane) (toroidal : ℝ) :
    coordinateDirection disk toroidal =
      coordinateDirection disk 0 + coordinateDirection 0 toroidal := by
  ext coordinate
  fin_cases coordinate <;> simp [coordinateDirection, vector]

theorem sampledCellCoordinateValue_fderiv (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ)
    (disk : Plane) (toroidal : ℝ) :
    fderiv ℝ
        (sampledCellCoordinateValue cellLength family period parameter.val)
        (vector 0 0 time) (coordinateDirection disk toroidal) =
      cellAxisCLM family.rho family.alpha family.delta parameter.val
        ((period : ℝ) * time)
        (normalizedFactor
          (family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time)))
        (family.tilt (sampledEpsilon period) parameter.val
          ((period : ℝ) * time)) disk := by
  rw [coordinateDirection_add]
  rw [map_add]
  rw [sampledCellCoordinateValue_fderiv_disk cellLength family period
    epsilonIn parameter time disk]
  rw [sampledCellCoordinateValue_fderiv_toroidal cellLength family period
    epsilonIn parameter time toroidal]
  exact add_zero _

noncomputable def rotationLinearMap (angle : ℝ) : Vec →ₗ[ℝ] Vec where
  toFun point := rotation angle point
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [rotation, vector] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [rotation, vector] <;> ring

noncomputable def rotationCLM (angle : ℝ) : Vec →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap (rotationLinearMap angle)

@[simp] theorem rotationCLM_apply (angle : ℝ) (point : Vec) :
    rotationCLM angle point = rotation angle point :=
  rfl

theorem rotation_cellAxisCLM (rho alpha delta parameter : ℝ)
    (period : ℕ) (time a : ℝ) (tilt disk : Plane) :
    rotation time
        (cellAxisCLM rho alpha delta parameter ((period : ℝ) * time)
          a tilt disk) =
      (a * (Grad.GeometryClosure.seedMatrix rho
          (sampledAlphaAngle period alpha delta parameter time)).mulVec
            (fun coordinate => disk coordinate) 0) •
          axisRadial time +
        (a * (Grad.GeometryClosure.seedMatrix rho
          (sampledAlphaAngle period alpha delta parameter time)).mulVec
            (fun coordinate => disk coordinate) 1) •
          axisVertical +
        planeDot tilt disk • axisTangent time := by
  have actionIdentity :
      seedAction rho alpha delta parameter ((period : ℝ) * time) disk =
        WithLp.toLp 2
          ((Grad.GeometryClosure.seedMatrix rho
            (sampledAlphaAngle period alpha delta parameter time)).mulVec
              (fun coordinate => disk coordinate)) := by
    rfl
  ext coordinate
  fin_cases coordinate <;>
    simp [cellAxisCLM_apply, actionIdentity, rotation, planeEmbedding,
      tangentDirection, basisVector, axisRadial, axisVertical, axisTangent,
      vector] <;> ring

def sampledPositionCoordinateValue (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ) (parameter : ℝ)
    (point : Vec) : Vec :=
  sampledPositionJointLift cellLength family period (parameter, point)

theorem sampledPositionCoordinateValue_differentiableAt_axis (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    DifferentiableAt ℝ
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (vector 0 0 time) := by
  let argument : ℝ × Vec := (parameter.val, vector 0 0 time)
  have argumentIn : argument ∈ sampledPhysicalCollar cellLength family := by
    refine ⟨parameter_mem_open cellLength family parameter, ?_⟩
    change planarPart (vector 0 0 time) ∈ Metric.ball 0 family.collarRadius
    have planarZero : planarPart (vector 0 0 time) = 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [planarPart, vector]
    rw [Metric.mem_ball, dist_zero_right, planarZero, norm_zero]
    linarith [family.collarLarge]
  have jointDifferentiable : DifferentiableAt ℝ
      (sampledPositionJointLift cellLength family period) argument :=
    ((sampledPositionJointLift_contDiffOn cellLength family period epsilonIn).contDiffAt
      ((sampledPhysicalCollar_isOpen cellLength family).mem_nhds
        argumentIn)).differentiableAt (by simp)
  have insertionDifferentiable : DifferentiableAt ℝ
      (fun point : Vec => (parameter.val, point)) (vector 0 0 time) := by
    fun_prop
  have composed := jointDifferentiable.comp (vector 0 0 time)
    insertionDifferentiable
  change DifferentiableAt ℝ
    (fun point : Vec =>
      sampledPositionJointLift cellLength family period (parameter.val, point))
    (vector 0 0 time)
  simpa [Function.comp_def, argument] using composed

theorem sampledPositionCoordinateValue_contDiffAt_axis (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    ContDiffAt ℝ 2
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (vector 0 0 time) := by
  let argument : ℝ × Vec := (parameter.val, vector 0 0 time)
  have argumentIn : argument ∈ sampledPhysicalCollar cellLength family := by
    refine ⟨parameter_mem_open cellLength family parameter, ?_⟩
    change planarPart (vector 0 0 time) ∈ Metric.ball 0 family.collarRadius
    have planarZero : planarPart (vector 0 0 time) = 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [planarPart, vector]
    rw [Metric.mem_ball, dist_zero_right, planarZero, norm_zero]
    linarith [family.collarLarge]
  have jointSmooth : ContDiffAt ℝ ∞
      (sampledPositionJointLift cellLength family period) argument :=
    (sampledPositionJointLift_contDiffOn cellLength family period epsilonIn).contDiffAt
      ((sampledPhysicalCollar_isOpen cellLength family).mem_nhds argumentIn)
  have insertionSmooth : ContDiffAt ℝ ∞
      (fun point : Vec => (parameter.val, point)) (vector 0 0 time) := by
    fun_prop
  have composed := jointSmooth.comp (vector 0 0 time) insertionSmooth
  change ContDiffAt ℝ 2
    (fun point : Vec =>
      sampledPositionJointLift cellLength family period (parameter.val, point))
    (vector 0 0 time)
  exact (by
    simpa [Function.comp_def, argument] using composed.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))

theorem sampledPositionCoordinateValue_fderiv_disk (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ)
    (disk : Plane) :
    fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter.val)
        (vector 0 0 time) (coordinateDirection disk 0) =
      rotation time
        (cellAxisCLM family.rho family.alpha family.delta parameter.val
          ((period : ℝ) * time)
          (normalizedFactor
            (family.tilt (sampledEpsilon period) parameter.val
              ((period : ℝ) * time)))
          (family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time)) disk) := by
  let coordinateBase : Vec := vector 0 0 time
  let diskInsertion : Plane → Vec :=
    (fun _ : Plane => coordinateBase) + physicalDiskCLM
  have insertionHasDerivative : HasFDerivAt diskInsertion physicalDiskCLM 0 := by
    simpa only [Pi.add_apply, zero_add] using
      (hasFDerivAt_const (x := (0 : Plane)) coordinateBase).add
        physicalDiskCLM.hasFDerivAt
  have insertionZero : diskInsertion 0 = vector 0 0 time := by
    simp [diskInsertion, coordinateBase, physicalDiskCLM_apply,
      coordinateDirection, vector]
  let cellFunction :=
    sampledCellCoordinateValue cellLength family period parameter.val
  let cellComposition : Plane → Vec := cellFunction ∘ diskInsertion
  have cellFunctionDifferentiable : DifferentiableAt ℝ cellFunction
      (diskInsertion 0) := by
    rw [insertionZero]
    exact sampledCellCoordinateValue_differentiableAt_axis cellLength family
      period epsilonIn parameter time
  have cellCompositionDifferentiable : DifferentiableAt ℝ cellComposition 0 :=
    cellFunctionDifferentiable.comp 0 insertionHasDerivative.differentiableAt
  have cellCompositionDerivative :
      fderiv ℝ cellComposition 0 =
        cellAxisCLM family.rho family.alpha family.delta parameter.val
          ((period : ℝ) * time)
          (normalizedFactor
            (family.tilt (sampledEpsilon period) parameter.val
              ((period : ℝ) * time)))
          (family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time)) := by
    rw [show cellComposition = cellFunction ∘ diskInsertion by rfl]
    rw [fderiv_comp (x := (0 : Plane)) cellFunctionDifferentiable
      insertionHasDerivative.differentiableAt]
    rw [insertionHasDerivative.fderiv, insertionZero]
    ext direction : 1
    simpa [cellFunction] using
      sampledCellCoordinateValue_fderiv_disk cellLength family period epsilonIn
        parameter time direction
  let radiusBase : Vec := (period * cellLength) • basisVector 0
  let rotationInput : Plane → Vec :=
    (fun _ : Plane => radiusBase) + cellComposition
  have rotationInputDifferentiable : DifferentiableAt ℝ rotationInput 0 := by
    dsimp [rotationInput]
    exact (differentiableAt_const radiusBase).add cellCompositionDifferentiable
  have rotationInputDerivative :
      fderiv ℝ rotationInput 0 =
        cellAxisCLM family.rho family.alpha family.delta parameter.val
          ((period : ℝ) * time)
          (normalizedFactor
            (family.tilt (sampledEpsilon period) parameter.val
              ((period : ℝ) * time)))
          (family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time)) := by
    dsimp [rotationInput]
    have constantDerivative :
        fderiv ℝ (fun _ : Plane => radiusBase) 0 = 0 :=
      (hasFDerivAt_const (x := (0 : Plane)) radiusBase).fderiv
    rw [fderiv_add (differentiableAt_const radiusBase)
      cellCompositionDifferentiable, constantDerivative, zero_add,
      cellCompositionDerivative]
  have rotatedDerivative :
      fderiv ℝ (rotationCLM time ∘ rotationInput) 0 =
        rotationCLM time ∘L
          cellAxisCLM family.rho family.alpha family.delta parameter.val
            ((period : ℝ) * time)
            (normalizedFactor
              (family.tilt (sampledEpsilon period) parameter.val
                ((period : ℝ) * time)))
            (family.tilt (sampledEpsilon period) parameter.val
              ((period : ℝ) * time)) := by
    rw [fderiv_comp (x := (0 : Plane)) (rotationCLM time).differentiableAt
      rotationInputDifferentiable]
    rw [(rotationCLM time).fderiv, rotationInputDerivative]
  have chartDifferentiableAtInsertion : DifferentiableAt ℝ
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (diskInsertion 0) := by
    rw [insertionZero]
    exact sampledPositionCoordinateValue_differentiableAt_axis cellLength family
      period epsilonIn parameter time
  have chartChain := fderiv_comp (x := (0 : Plane))
    chartDifferentiableAtInsertion insertionHasDerivative.differentiableAt
  rw [insertionZero, insertionHasDerivative.fderiv] at chartChain
  have chartCompositionEquality :
      sampledPositionCoordinateValue cellLength family period parameter.val ∘
          diskInsertion = rotationCLM time ∘ rotationInput := by
    funext point
    simp [Function.comp_def, sampledPositionCoordinateValue,
      sampledPositionJointLift, sampledPositionRotationInput,
      uncurriedRotation, rotationInput, radiusBase, cellComposition,
      cellFunction, sampledCellCoordinateValue, diskInsertion, coordinateBase,
      physicalDiskCLM_apply, coordinateDirection, vector]
  rw [chartCompositionEquality, rotatedDerivative] at chartChain
  have evaluated := congrArg (fun derivative : Plane →L[ℝ] Vec =>
    derivative disk) chartChain
  simpa using evaluated.symm

theorem axisRadial_shift_hasDerivAt (time : ℝ) :
    HasDerivAt (fun offset : ℝ => axisRadial (time + offset))
      (axisTangent time) 0 := by
  have angleDerivative : HasDerivAt (fun offset : ℝ => time + offset) 1 0 :=
    (hasDerivAt_id (x := (0 : ℝ))).const_add time
  have coordinateDerivative :=
    (angleDerivative.cos.smul_const (basisVector 0)).add
      (angleDerivative.sin.smul_const (basisVector 1))
  have functionEquality :
      ((fun offset : ℝ => Real.cos (time + offset) • basisVector 0) +
        fun offset : ℝ => Real.sin (time + offset) • basisVector 1) =
      (fun offset : ℝ => axisRadial (time + offset)) := by
    funext offset
    ext coordinate
    fin_cases coordinate <;>
      simp [axisRadial, basisVector, vector]
  have derivativeEquality :
      (-Real.sin (time + 0) * 1) • basisVector 0 +
          (Real.cos (time + 0) * 1) • basisVector 1 =
        axisTangent time := by
    ext coordinate
    fin_cases coordinate <;>
      simp [axisTangent, basisVector, vector]
  rw [functionEquality, derivativeEquality] at coordinateDerivative
  exact coordinateDerivative

theorem radius_axisRadial_shift_hasDerivAt (radius time : ℝ) :
    HasDerivAt (fun offset : ℝ => radius • axisRadial (time + offset))
      (radius • axisTangent time) 0 :=
  (axisRadial_shift_hasDerivAt time).const_smul radius

theorem rotation_major_axis (radius time : ℝ) :
    rotation time (radius • basisVector 0) =
      radius • axisRadial time := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rotation, basisVector, axisRadial, vector] <;> ring

theorem sampledPosition_axis (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    sampledPositionLift cellLength family period parameter.val 0 time =
      (period * cellLength) • axisRadial time := by
  rw [sampledPositionLift,
    cell_value_axis_zero cellLength family period epsilonIn parameter]
  simp only [add_zero]
  exact rotation_major_axis (period * cellLength) time

theorem sampledPositionCoordinateValue_fderiv_toroidal (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time toroidal : ℝ) :
    fderiv ℝ
        (sampledPositionCoordinateValue cellLength family period parameter.val)
        (vector 0 0 time) (coordinateDirection 0 toroidal) =
      ((period : ℝ) * cellLength * toroidal) • axisTangent time := by
  let coordinateBase : Vec := vector 0 0 time
  let toroidalInsertion : ℝ → Vec :=
    (fun _ : ℝ => coordinateBase) + physicalToroidalCLM
  have insertionHasDerivative :
      HasFDerivAt toroidalInsertion physicalToroidalCLM 0 := by
    simpa only [Pi.add_apply, zero_add] using
      (hasFDerivAt_const (x := (0 : ℝ)) coordinateBase).add
        physicalToroidalCLM.hasFDerivAt
  have insertionZero : toroidalInsertion 0 = vector 0 0 time := by
    simp [toroidalInsertion, coordinateBase, physicalToroidalCLM_apply,
      coordinateDirection, vector]
  have chartDifferentiableAtInsertion : DifferentiableAt ℝ
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (toroidalInsertion 0) := by
    rw [insertionZero]
    exact sampledPositionCoordinateValue_differentiableAt_axis cellLength family
      period epsilonIn parameter time
  have chainRule := fderiv_comp (x := (0 : ℝ))
    chartDifferentiableAtInsertion insertionHasDerivative.differentiableAt
  rw [insertionZero, insertionHasDerivative.fderiv] at chainRule
  have compositionEquality :
      sampledPositionCoordinateValue cellLength family period parameter.val ∘
          toroidalInsertion =
        fun offset : ℝ =>
          ((period : ℝ) * cellLength) • axisRadial (time + offset) := by
    funext offset
    have insertionFormula :
        toroidalInsertion offset = vector 0 0 (time + offset) := by
      ext coordinate
      fin_cases coordinate <;>
        simp [toroidalInsertion, coordinateBase, physicalToroidalCLM_apply,
          coordinateDirection, vector]
    change sampledPositionCoordinateValue cellLength family period parameter.val
        (toroidalInsertion offset) = _
    rw [insertionFormula]
    change sampledPositionJointLift cellLength family period
        (parameter.val, vector 0 0 (time + offset)) = _
    rw [sampledPositionJointLift_eq]
    have planarZero : planarPart (vector 0 0 (time + offset)) = 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [planarPart, vector]
    rw [planarZero]
    have physicalTime : (vector 0 0 (time + offset) : Vec) 2 =
        time + offset := by
      simp [vector]
    rw [physicalTime]
    exact sampledPosition_axis cellLength family period epsilonIn parameter _
  rw [compositionEquality] at chainRule
  have axisDerivative :=
    (radius_axisRadial_shift_hasDerivAt
      ((period : ℝ) * cellLength) time).hasFDerivAt.fderiv
  rw [axisDerivative] at chainRule
  have evaluated := congrArg (fun derivative : ℝ →L[ℝ] Vec =>
    derivative toroidal) chainRule
  simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using evaluated.symm

theorem sampledPosition_hasAxisDerivative (cellLength : ℝ)
    (family : CellSolutionFamily cellLength) (period : ℕ)
    (epsilonIn : sampledEpsilon period ∈
      Set.Ioo (-family.epsilonZero) family.epsilonZero)
    (parameter : Set.Icc family.lower family.upper) (time : ℝ) :
    HasAxisDerivative
      (sampledPositionCoordinateValue cellLength family period parameter.val)
      (vector 0 0 time) ((period : ℝ) * cellLength) time
      (normalizedFactor
        (family.tilt (sampledEpsilon period) parameter.val
          ((period : ℝ) * time)))
      (Grad.GeometryClosure.seedMatrix family.rho
        (sampledAlphaAngle period family.alpha family.delta parameter.val time))
      (fun coordinate =>
        family.tilt (sampledEpsilon period) parameter.val
          ((period : ℝ) * time) coordinate) := by
  intro disk toroidal
  let diskPlane : Plane := WithLp.toLp 2 disk
  have directionIdentity :
      coordinateDirection disk toroidal =
        coordinateDirection diskPlane toroidal := by
    ext coordinate
    fin_cases coordinate <;>
      simp [coordinateDirection, diskPlane, vector]
  rw [directionIdentity, coordinateDirection_add, map_add]
  rw [sampledPositionCoordinateValue_fderiv_disk cellLength family period
    epsilonIn parameter time diskPlane]
  rw [sampledPositionCoordinateValue_fderiv_toroidal cellLength family period
    epsilonIn parameter time toroidal]
  rw [rotation_cellAxisCLM]
  have matrixIdentity :
      (Grad.GeometryClosure.seedMatrix family.rho
          (sampledAlphaAngle period family.alpha family.delta parameter.val time)).mulVec
          (fun coordinate => diskPlane coordinate) =
        (Grad.GeometryClosure.seedMatrix family.rho
          (sampledAlphaAngle period family.alpha family.delta parameter.val time)).mulVec
          disk := by
    rfl
  have dotIdentity :
      planeDot
          (family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time)) diskPlane =
        (fun coordinate =>
          family.tilt (sampledEpsilon period) parameter.val
            ((period : ℝ) * time) coordinate) ⬝ᵥ disk := by
    simp [planeDot, dotProduct, Fin.sum_univ_two, diskPlane]
  rw [matrixIdentity, dotIdentity]
  calc
    _ =
        (normalizedFactor
            (family.tilt (sampledEpsilon period) parameter.val
              ((period : ℝ) * time)) *
          (Grad.GeometryClosure.seedMatrix family.rho
              (sampledAlphaAngle period family.alpha family.delta parameter.val
                time)).mulVec disk 0) • axisRadial time +
        (normalizedFactor
            (family.tilt (sampledEpsilon period) parameter.val
              ((period : ℝ) * time)) *
          (Grad.GeometryClosure.seedMatrix family.rho
              (sampledAlphaAngle period family.alpha family.delta parameter.val
                time)).mulVec disk 1) • axisVertical +
        ((fun coordinate =>
            family.tilt (sampledEpsilon period) parameter.val
              ((period : ℝ) * time) coordinate) ⬝ᵥ disk) • axisTangent time +
        (((period : ℝ) * cellLength) * toroidal) • axisTangent time := by
          rfl
    _ = _ := by
      rw [add_assoc]
      rw [← add_smul]

end Grad.MainAssembly.SampledAxisBasics
