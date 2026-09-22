import AKDE14ConstructedTiltSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
open Set
open scoped ContDiff
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient Grad.AxisSplit
open Grad.Q24Realization
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit Grad.GeometryClosure Grad.MainTarget

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

theorem realSeedAction_joint_smooth :
    ContDiffOn ℝ ∞ (fun point : Seed.Parameters × (Plane × ℝ) =>
      seedAction (point.1 0) (point.1 1) (point.1 2) (point.1 3) point.2.2 point.2.1)
      (Seed.parameterDomain ×ˢ Set.univ) := by
  have plus : ContDiffOn ℝ ∞ (fun point : Seed.Parameters × (Plane × ℝ) => Real.sqrt (1+point.1 0))
      (Seed.parameterDomain ×ˢ Set.univ) := by
    apply (show ContDiffOn ℝ ∞ (fun point : Seed.Parameters × (Plane × ℝ) => 1+point.1 0) _ from by fun_prop).sqrt
    intro point member
    have small := (abs_lt.mp (show |point.1 0| < 1 from member.1)).1
    linarith
  have minus : ContDiffOn ℝ ∞ (fun point : Seed.Parameters × (Plane × ℝ) => Real.sqrt (1-point.1 0))
      (Seed.parameterDomain ×ˢ Set.univ) := by
    apply (show ContDiffOn ℝ ∞ (fun point : Seed.Parameters × (Plane × ℝ) => 1-point.1 0) _ from by fun_prop).sqrt
    intro point member
    have small := (abs_lt.mp (show |point.1 0| < 1 from member.1)).2
    linarith
  rw [contDiffOn_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [seedAction,harmonicSeedMatrix,seedMatrix,rotatedDiagonal_entries,seedAngle,
      dotProduct,Fin.sum_univ_two] <;> fun_prop

theorem constructedCellRemainder_joint_smooth (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw) :
    ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      constructedCellRemainder scale point.1 point.2.1 point.2.2) (constructedCellDomain scale) := by
  have insertion : ContDiff ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) => (point.1,point.2.2)) := by fun_prop
  have tilt := (constructedTilt_joint_smooth scale leftLaw).comp (s := constructedCellDomain scale) insertion.contDiffOn
    (fun point member => ⟨member.1,mem_univ _⟩)
  have factor := (constructedNormalizedFactor_joint_smooth scale leftLaw).comp (s := constructedCellDomain scale) insertion.contDiffOn
    (fun point member => ⟨member.1,mem_univ _⟩)
  have seed := realSeedAction_joint_smooth.comp (s := constructedCellDomain scale)
    (show ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) => (point.1.1,point.2)) _ by fun_prop)
    (fun point member => ⟨(scale.parameterLimit_admissible point.1 member.1).1,mem_univ _⟩)
  have embedded : ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      planeEmbedding (seedAction (point.1.1 0) (point.1.1 1) (point.1.1 2) (point.1.1 3) point.2.2 point.2.1))
      (constructedCellDomain scale) := by
    rw [contDiffOn_piLp]
    intro coordinate
    fin_cases coordinate
    · exact ((contDiffOn_piLp 2).mp seed) 0
    · exact contDiffOn_const
    · exact ((contDiffOn_piLp 2).mp seed) 1
  have dot : ContDiffOn ℝ ∞ (fun point : OriginalFiniteParameter × (SpatialPlane × ℝ) =>
      planeDot (constructedTilt scale point.1 point.2.2) point.2.1) (constructedCellDomain scale) := by
    simp only [planeDot,Fin.sum_univ_two]
    exact (((contDiffOn_piLp 2).mp tilt 0).mul (by fun_prop)).add
      (((contDiffOn_piLp 2).mp tilt 1).mul (by fun_prop))
  exact (constructedCellVector_joint_smooth scale leftLaw).sub ((factor.smul embedded).add (dot.smul contDiffOn_const))

theorem originalRealTilt_periodic (family : TangentCoefficient parameters) (cell : ℝ) :
    originalRealTilt family (cell+2*Real.pi)=originalRealTilt family cell := by
  unfold originalRealTilt planarValue
  simp only [axialPhase_eq_character,AddCircle.coe_add_period]

theorem realSeedAction_periodic (rho alpha delta parameter cell : ℝ) (point : Plane) :
    seedAction rho alpha delta parameter (cell+2*Real.pi) point = seedAction rho alpha delta parameter cell point := by
  unfold seedAction harmonicSeedMatrix
  rw [seedAngle_periodic_shift alpha delta parameter cell (2*Real.pi) ⟨1,by simp⟩]

theorem constructedCellFields_periodic (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (disk : SpatialPlane) (cell : ℝ) :
    constructedCellVector scale point disk (cell+2*Real.pi)=constructedCellVector scale point disk cell ∧
    constructedCellPotential scale point disk (cell+2*Real.pi)=constructedCellPotential scale point disk cell ∧
    constructedTilt scale point (cell+2*Real.pi)=constructedTilt scale point cell ∧
    constructedCellRemainder scale point disk (cell+2*Real.pi)=constructedCellRemainder scale point disk cell := by
  have vector := (constructedRealFields_periodic scale point disk cell).1
  have scalar := congrArg (fun value : EuclideanSpace ℝ (Fin 1) => value 0)
    (constructedRealFields_periodic scale point disk cell).2
  have tilt := originalRealTilt_periodic (smoothingChartCore parameters (scale.parameterLimit point).val).1 cell
  refine ⟨vector,scalar,tilt,?_⟩
  unfold constructedCellRemainder
  rw [show constructedTilt scale point (cell+2*Real.pi)=constructedTilt scale point cell from tilt,
    show constructedCellVector scale point disk (cell+2*Real.pi)=constructedCellVector scale point disk cell from vector,
    realSeedAction_periodic]

end Grad.OriginalCellFamily
