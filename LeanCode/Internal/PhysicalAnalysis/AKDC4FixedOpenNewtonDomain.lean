import AKDC3ActualNewtonStepContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward Grad.NashMoser.Numeric
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.NashMoser.InverseCalculus

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

namespace OriginalNewtonScale
variable (scale : OriginalNewtonScale inverse)

/-- One open parameter domain, fixed for all stages, completed grades and
spatial derivatives. Actual strict residual smallness gives membership. -/
def openParameterDomain : Set OriginalFiniteParameter := interior scale.parameterDomain

theorem openParameterDomain_isOpen : IsOpen scale.openParameterDomain := isOpen_interior

theorem openParameterDomain_subset : scale.openParameterDomain ⊆ scale.parameterDomain := interior_subset

theorem initialResidual_continuousOn : ContinuousOn (fun point => inverse.residualSize point 0)
    (interior neighborhood.parameterDomain) := by
  have admissible : ∀ point ∈ interior neighborhood.parameterDomain,
      point.1 ∈ Seed.parameterDomain ∧ ChartAxisCondition (smoothingChartCore parameters
        (0 : stateSmoothRange parameters reference inside).val) := by
    intro point member
    exact ⟨neighborhood.patchInside (neighborhood.seedInside point (interior_subset member)),
      neighborhood.axis 0 (by rw [map_zero]; linarith [neighborhood.radiusPositive])⟩
  have actual := originalNonlinearSource_continuousOn (cellLength := cellLength)
    (interior neighborhood.parameterDomain) (fun _ => (0 : stateSmoothRange parameters reference inside))
    admissible (base+loss) (by have := neighborhood.baseLarge; omega) continuousOn_const
  exact actual.norm

theorem openParameterDomain_of_residual_lt (point : OriginalFiniteParameter)
    (member : point ∈ interior neighborhood.parameterDomain)
    (small : inverse.residualSize point 0 < scale.initial ^ (-initialDecay loss)) :
    point ∈ scale.openParameterDomain := by
  rw [openParameterDomain,mem_interior_iff_mem_nhds]
  change neighborhood.parameterDomain ∩ {point | inverse.residualSize point 0 ≤ scale.initial ^ (-initialDecay loss)} ∈ 𝓝 point
  refine inter_mem (mem_of_superset (isOpen_interior.mem_nhds member) interior_subset) ?_
  have continuous := (initialResidual_continuousOn (inverse := inverse) point member).continuousAt (isOpen_interior.mem_nhds member)
  filter_upwards [continuous.eventually (gt_mem_nhds small)] with location bound
  exact le_of_lt bound

theorem openParameterDomain_contains_zero (point : OriginalFiniteParameter)
    (member : point ∈ interior neighborhood.parameterDomain)
    (zero : originalNonlinearSource parameters cellLength reference inside point 0 = 0) :
    point ∈ scale.openParameterDomain := by
  apply scale.openParameterDomain_of_residual_lt point member
  change sourceSize parameters base loss (originalNonlinearSource parameters cellLength reference inside point 0) < _
  rw [zero,map_zero]
  exact Real.rpow_pos_of_pos (by linarith [scale.initialLarge]) _

/-- Totalization for ordinary finite-parameter calculus. On the fixed open
domain this is literally the accepted CY finite stage, with the SAME value. -/
def parameterIterate (index : ℕ) (point : OriginalFiniteParameter) : stateSmoothRange parameters reference inside := by
  classical
  exact if member : point ∈ scale.parameterDomain then scale.iterate point member index else 0

def parameterLimit (point : OriginalFiniteParameter) : stateSmoothRange parameters reference inside := by
  classical
  exact if member : point ∈ scale.parameterDomain then scale.originalLimit ⟨point,member⟩ else 0

theorem parameterIterate_same (index : ℕ) (point : OriginalFiniteParameter) (member : point ∈ scale.parameterDomain) :
    scale.parameterIterate index point = scale.iterate point member index := by
  rw [parameterIterate,dif_pos member]

theorem parameterLimit_same (point : OriginalFiniteParameter) (member : point ∈ scale.parameterDomain) :
    scale.parameterLimit point = scale.originalLimit ⟨point,member⟩ := by
  rw [parameterLimit,dif_pos member]

theorem parameterIterate_zero (point : OriginalFiniteParameter) : scale.parameterIterate 0 point = 0 := by
  classical
  unfold parameterIterate
  split
  · exact scale.iterate_zero _ _
  · rfl

theorem parameterIterate_step (index : ℕ) (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    scale.parameterIterate (index+1) point = smoothedNewtonNext parameters reference inside cellLength point
      (newtonTime scale.initial index) (scale.parameterIterate index point)
        (inverse.map point (scale.parameterIterate index point)) := by
  rw [scale.parameterIterate_same (index+1) point (scale.openParameterDomain_subset member),
    scale.parameterIterate_same index point (scale.openParameterDomain_subset member),scale.iterate_step]
  rfl

theorem parameterIterate_low (index : ℕ) (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    stateSize parameters reference inside base 0 (scale.parameterIterate index point) ≤ 2*neighborhood.radius := by
  rw [scale.parameterIterate_same index point (scale.openParameterDomain_subset member)]
  exact ((stateSize_mono parameters reference inside base (Nat.zero_le loss) _).trans
    (scale.iterate_low point (scale.openParameterDomain_subset member) index)).trans (by linarith [neighborhood.radiusPositive])

theorem parameterLimit_low (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    stateSize parameters reference inside base 0 (scale.parameterLimit point) ≤ 2*neighborhood.radius := by
  rw [scale.parameterLimit_same point (scale.openParameterDomain_subset member)]
  exact ((stateSize_mono parameters reference inside base (Nat.zero_le loss) _).trans
    (scale.originalLimit_low ⟨point,scale.openParameterDomain_subset member⟩)).trans (by linarith [neighborhood.radiusPositive])

theorem parameterLimit_exact_zero (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain) :
    originalNonlinearSource parameters cellLength reference inside point (scale.parameterLimit point) = 0 := by
  rw [scale.parameterLimit_same point (scale.openParameterDomain_subset member)]
  exact scale.originalLimit_exact_zero ⟨point,scale.openParameterDomain_subset member⟩

end OriginalNewtonScale
end Grad.NashMoser.OriginalIteration
