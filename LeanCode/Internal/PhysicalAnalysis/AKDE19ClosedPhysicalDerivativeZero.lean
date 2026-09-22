import AKDE18UniformPhysicalDerivativeBound
import AKDE15ConstructedRemainderSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff Topology
namespace Grad.OriginalCellFamily
open Grad.ClosedJets Grad.PhysicalFamily Grad.MainTarget

def physicalCoordinatePointCLM : SpatialPlane × ℝ →L[ℝ] Vec :=
  LinearMap.toContinuousLinearMap {
    toFun := fun point => coordinatePoint point.1 point.2
    map_add' := by intro first second; apply PiLp.ext; intro coordinate; fin_cases coordinate <;> rfl
    map_smul' := by intro scalar point; apply PiLp.ext; intro coordinate; fin_cases coordinate <;> rfl }

def physicalCoordinateDiskCLM : Vec →L[ℝ] SpatialPlane :=
  LinearMap.toContinuousLinearMap {
    toFun := coordinateDisk
    map_add' := by intro first second; apply PiLp.ext; intro coordinate; fin_cases coordinate <;> rfl
    map_smul' := by intro scalar point; apply PiLp.ext; intro coordinate; fin_cases coordinate <;> rfl }

theorem physicalCoordinateDisk_point (point : SpatialPlane) (cell : ℝ) :
    coordinateDisk (coordinatePoint point cell)=point := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem physicalCoordinatePoint_disk (point : Vec) : coordinatePoint (coordinateDisk point) (point 1)=point := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem physicalCoordinateCollar_isOpen (radius : ℝ) : IsOpen (coordinateCollar radius) :=
  isOpen_lt physicalCoordinateDiskCLM.continuous.norm continuous_const

def physicalCompactCell : Set Vec :=
  physicalCoordinatePointCLM '' (Metric.closedBall (0 : SpatialPlane) 1 ×ˢ Icc (0 : ℝ) (2*Real.pi))

theorem physicalCompactCell_isCompact : IsCompact physicalCompactCell :=
  ((isCompact_closedBall (0 : SpatialPlane) 1).prod isCompact_Icc).image physicalCoordinatePointCLM.continuous

theorem physicalCompactCell_included : physicalCompactCell ⊆ coordinateCollar (4/3) := by
  rintro point ⟨⟨disk,cell⟩,⟨diskIn,_⟩,rfl⟩
  change ‖coordinateDisk (coordinatePoint disk cell)‖ < 4/3
  rw [physicalCoordinateDisk_point]
  have bound : ‖disk‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using diskIn
  linarith

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Vanishing on the actual closed disk implies vanishing of every genuine
physical derivative there, including the outer boundary. No polynomial
extension identity outside the disk is asserted. -/
theorem physicalClosedDisk_zero_derivative (field : Vec → Y)
    (smooth : ContDiffOn ℝ ∞ field (coordinateCollar (4/3)))
    (zero : ∀ point : Grad.ClosedJets.ClosedDisk, ∀ cell : ℝ, field (coordinatePoint point.val cell)=0)
    (order : ℕ) (point : Grad.ClosedJets.ClosedDisk) (cell : ℝ) :
    iteratedFDeriv ℝ order field (coordinatePoint point.val cell)=0 := by
  have interiorZero : EqOn field (fun _ => (0 : Y)) (coordinateCollar 1) := by
    intro query member
    have inside : ‖coordinateDisk query‖ < 1 := member
    have result := zero ⟨coordinateDisk query,inside.le⟩ (query 1)
    rwa [physicalCoordinatePoint_disk] at result
  have derivativeContinuous : Continuous (fun disk : Grad.ClosedJets.ClosedDisk =>
      iteratedFDeriv ℝ order field (coordinatePoint disk.val cell)) := by
    apply continuous_iff_continuousAt.mpr
    intro disk
    have included : coordinatePoint disk.val cell ∈ coordinateCollar (4/3) := by
      change ‖coordinateDisk (coordinatePoint disk.val cell)‖ < 4/3
      rw [physicalCoordinateDisk_point]
      exact disk.property.trans_lt (by norm_num)
    have actual := (smooth.contDiffAt ((physicalCoordinateCollar_isOpen (4/3)).mem_nhds included)).iteratedFDeriv_right
      (m := ∞) (i := order) (by norm_cast)
    have outer : ContinuousAt (iteratedFDeriv ℝ order field) (coordinatePoint disk.val cell) := actual.continuousAt
    have insertion : Continuous (fun query : Grad.ClosedJets.ClosedDisk => coordinatePoint query.val cell) :=
      physicalCoordinatePointCLM.continuous.comp (continuous_subtype_val.prodMk (continuous_const (y := cell)))
    exact outer.comp (f := fun query : Grad.ClosedJets.ClosedDisk => coordinatePoint query.val cell) (x := disk) insertion.continuousAt
  let first : ContinuousMap Grad.ClosedJets.ClosedDisk (ContinuousMultilinearMap ℝ (fun _ : Fin order => Vec) Y) :=
    ⟨fun disk => iteratedFDeriv ℝ order field (coordinatePoint disk.val cell),derivativeContinuous⟩
  let second : ContinuousMap Grad.ClosedJets.ClosedDisk (ContinuousMultilinearMap ℝ (fun _ : Fin order => Vec) Y) :=
    ⟨fun _ => 0,continuous_const⟩
  have equality := continuousMap_eq_of_openDisk first second (fun disk diskIn => by
    have location : coordinatePoint disk.val cell ∈ coordinateCollar 1 := by
      change ‖coordinateDisk (coordinatePoint disk.val cell)‖ < 1
      rw [physicalCoordinateDisk_point]
      exact diskIn
    have agreement := iteratedFDerivWithin_congr (𝕜 := ℝ) interiorZero location order
    rw [iteratedFDerivWithin_of_isOpen order (physicalCoordinateCollar_isOpen 1) location,
      iteratedFDerivWithin_of_isOpen order (physicalCoordinateCollar_isOpen 1) location] at agreement
    simpa [first,second] using agreement)
  exact congrArg (fun function : ContinuousMap Grad.ClosedJets.ClosedDisk
    (ContinuousMultilinearMap ℝ (fun _ : Fin order => Vec) Y) => function point) equality

end Grad.OriginalCellFamily
