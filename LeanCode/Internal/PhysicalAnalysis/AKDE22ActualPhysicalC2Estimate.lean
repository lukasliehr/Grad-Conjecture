import AKDE21OriginalParameterWindow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff Topology
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.PhysicalFamily Grad.MainTarget
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

namespace ConstructedParameterWindow
variable (scale : OriginalNewtonScale inverse) (window : ConstructedParameterWindow scale)

theorem physicalC2_bound (leftLaw : inverse.LeftLaw)
    (zero : ∀ parameter ∈ Ioo window.parameterLower window.parameterUpper,
      scale.parameterLimit (cellFiniteParameter window.rho window.alpha window.delta 0 parameter)=0) :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ epsilon : ℝ, |epsilon| ≤ window.radius/2 →
      ∀ parameter ∈ Icc window.lower window.upper,
        circleC2Seminorm (window.tilt scale epsilon parameter) +
          cellC2Seminorm (window.remainder scale epsilon parameter) ≤ bound * |epsilon| := by
  have zeroIn : (0 : ℝ) ∈ Ioo (-window.radius) window.radius := ⟨by linarith [window.positive],window.positive⟩
  have smooth := window.fields_smooth scale leftLaw
  have tiltZero (parameter : ℝ) (parameterIn : parameter ∈ Icc window.lower window.upper)
      (cell : ℝ) (_cellIn : cell ∈ Icc (0 : ℝ) (2*Real.pi)) (order : ℕ) :
      iteratedFDeriv ℝ order (fun cell => uncurriedCircle (window.tilt scale) (0,(parameter,cell))) cell=0 := by
    have entire : (fun cell => uncurriedCircle (window.tilt scale) (0,(parameter,cell))) = fun _ => (0 : Plane) := by
      funext cell
      exact constructedTilt_of_limit_zero scale _ (zero parameter (window.parameter_mem scale parameterIn)) cell
    rw [entire]
    simp
  obtain ⟨tiltBound,tiltLarge,tiltEstimate⟩ := compactC2_zero_bound window.radius window.positive
    window.parameterLower window.parameterUpper window.lower window.upper window.parameterContains
    Set.univ isOpen_univ (Icc (0 : ℝ) (2*Real.pi)) isCompact_Icc (fun _ _ => mem_univ _)
    (uncurriedCircle (window.tilt scale)) smooth.2.2.2 tiltZero
  have remainderZero (parameter : ℝ) (parameterIn : parameter ∈ Icc window.lower window.upper)
      (point : Vec) (pointIn : point ∈ physicalCompactCell) (order : ℕ) :
      iteratedFDeriv ℝ order (fun spatial => uncurriedCell (window.remainder scale) (0,(parameter,spatial))) point=0 := by
    have parameterOpen := window.parameter_mem scale parameterIn
    have pointMember := window.included 0 zeroIn parameter parameterOpen
    have fieldSmooth : ContDiffOn ℝ ∞
        (fun spatial : Vec => uncurriedCell (window.remainder scale) (0,(parameter,spatial))) (coordinateCollar (4/3)) :=
      smooth.2.2.1.comp (show ContDiffOn ℝ ∞ (fun spatial : Vec => (0,(parameter,spatial))) _ by fun_prop)
        (fun _ member => ⟨zeroIn,parameterOpen,member⟩)
    have zeroValues (disk : Grad.ClosedJets.ClosedDisk) (cell : ℝ) :
        uncurriedCell (window.remainder scale) (0,(parameter,coordinatePoint disk.val cell))=0 := by
      change constructedCellRemainder scale _ (coordinateDisk (coordinatePoint disk.val cell))
        ((coordinatePoint disk.val cell) 1)=0
      rw [physicalCoordinateDisk_point]
      exact constructedRemainder_of_limit_zero scale _ pointMember (zero parameter parameterOpen) disk cell
    rcases pointIn with ⟨⟨disk,cell⟩,⟨diskIn,_⟩,rfl⟩
    exact physicalClosedDisk_zero_derivative _ fieldSmooth zeroValues order
      ⟨disk,by simpa only [Metric.mem_closedBall,dist_zero_right,closedUnitDisk,mem_ofPred_eq] using diskIn⟩ cell
  obtain ⟨remainderBound,remainderLarge,remainderEstimate⟩ := compactC2_zero_bound window.radius window.positive
    window.parameterLower window.parameterUpper window.lower window.upper window.parameterContains
    (coordinateCollar (4/3)) (physicalCoordinateCollar_isOpen (4/3)) physicalCompactCell physicalCompactCell_isCompact
    physicalCompactCell_included (uncurriedCell (window.remainder scale)) smooth.2.2.1 remainderZero
  refine ⟨tiltBound+remainderBound,by linarith,?_⟩
  intro epsilon small parameter parameterIn
  have tiltUpper : circleC2Seminorm (window.tilt scale epsilon parameter) ≤ tiltBound*|epsilon| := by
    apply csSup_le
    · exact ⟨‖iteratedFDeriv ℝ 0 (window.tilt scale epsilon parameter) 0‖,0,0,⟨le_rfl,by positivity⟩,rfl⟩
    · rintro value ⟨order,cell,cellIn,rfl⟩
      exact tiltEstimate epsilon small parameter parameterIn cell cellIn order
  have remainderUpper : cellC2Seminorm (window.remainder scale epsilon parameter) ≤ remainderBound*|epsilon| := by
    apply csSup_le
    · exact ⟨‖iteratedFDeriv ℝ 0 (fun point : Vec => window.remainder scale epsilon parameter (coordinateDisk point) (point 1))
        (coordinatePoint 0 0)‖,0,0,0,by simp,⟨le_rfl,by positivity⟩,rfl⟩
    · rintro value ⟨order,disk,cell,diskIn,cellIn,rfl⟩
      apply remainderEstimate epsilon small parameter parameterIn (coordinatePoint disk cell)
      exact ⟨(disk,cell),⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using diskIn,cellIn⟩,rfl⟩
  calc
    _ ≤ tiltBound*|epsilon|+remainderBound*|epsilon| := add_le_add tiltUpper remainderUpper
    _ = (tiltBound+remainderBound)*|epsilon| := by ring

end ConstructedParameterWindow
end Grad.OriginalCellFamily
