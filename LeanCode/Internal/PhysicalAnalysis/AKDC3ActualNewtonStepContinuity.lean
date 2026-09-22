import AKDC2OriginalInverseNeighborhoodTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.NashMoser.InverseCalculus

attribute [local irreducible] originalNonlinearSource literalPhysicalSmoothForward originalStateSmoothing

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}

/-- Actual QYP continuity of the literal original residual along a continuous
original branch, at its displayed six-grade input loss. -/
theorem originalNonlinearSource_continuousOn
    (domain : Set OriginalFiniteParameter)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference inside)
    (admissible : ∀ point ∈ domain, point.1 ∈ Seed.parameterDomain ∧
      ChartAxisCondition (smoothingChartCore parameters (branch point).val))
    (grade : ℕ) (large : 3 ≤ grade)
    (continuous : ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside (grade+6)
      (realHighLarge grade) (branch point)) domain) :
    ContinuousOn (fun point => sourceSmoothEmbedding parameters grade large
      (originalNonlinearSource parameters cellLength reference inside point (branch point))) domain := by
  have mixed := (originalMixedBranch_contDiffOn parameters reference inside branch (grade+6)
    (realHighLarge grade) 0 domain (contDiffOn_zero.mpr continuous)).continuousOn
  have composed := (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference inside grade large).continuousOn.comp
    mixed (fun point member => (realMixedDomain_core_iff parameters reference inside (grade+6)
      (realHighLarge grade) (point.1,point.2,branch point)).mpr (admissible point member))
  apply composed.congr
  intro point member
  exact (originalNonlinearSource_completed parameters cellLength reference inside point (branch point)
    (admissible point member).1 (admissible point member).2 grade large)

namespace OriginalNewtonInverse
variable (inverse : OriginalNewtonInverse neighborhood cellLength loss)
    (leftLaw : inverse.LeftLaw)
    (domain : Set OriginalFiniteParameter) (openDomain : IsOpen domain)
    (included : domain ⊆ neighborhood.parameterDomain)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference inside)
    (low : ∀ point ∈ domain, stateSize parameters reference inside base 0 (branch point) ≤ 2*neighborhood.radius)
    (continuous : ∀ grade, ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside
      (grade+4) (branchGrade_large grade) (branch point)) domain)

include leftLaw openDomain included low continuous in
/-- The actual inverse applied to the actual residual is continuous at every
original grade. CZ derives operator continuity from BOTH core inverse laws;
no continuity or differentiability of the chosen inverse is postulated. -/
theorem appliedInverse_continuousOn (grade : ℕ) :
    ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside (grade+4)
      (branchGrade_large grade) (inverse.map point (branch point)
        (originalNonlinearSource parameters cellLength reference inside point (branch point)))) domain := by
  let currentInverse := fun point => inverse.map point (branch point)
  have admissible : ∀ point ∈ domain, point.1 ∈ Seed.parameterDomain ∧
      ChartAxisCondition (smoothingChartCore parameters (branch point).val) := by
    intro point member
    exact ⟨neighborhood.patchInside (neighborhood.seedInside point (included member)),
      neighborhood.axis _ (low point member)⟩
  have tame := inverse.branch_tame domain included branch low
  have right : ∀ point (member : point ∈ domain), ∀ source,
      literalPhysicalSmoothForward parameters cellLength reference inside point.1 (admissible point member).1
        (point.2,branch point) (admissible point member).2 (currentInverse point source) = source :=
    fun point member => inverse.right point (included member) (branch point) (low point member)
  have left : ∀ point (member : point ∈ domain), ∀ state,
      currentInverse point (literalPhysicalSmoothForward parameters cellLength reference inside point.1
        (admissible point member).1 (point.2,branch point) (admissible point member).2 state) = state :=
    fun point member => leftLaw.left point (included member) (branch point) (low point member)
  obtain ⟨input,ordered,operatorContinuous⟩ := originalCompletedBranchInverse_continuous parameters reference inside
    branch domain inverse.parameterLoss currentInverse inverse.constant inverse.nonnegative tame
    cellLength admissible right left openDomain continuous grade
  have residualContinuous := originalNonlinearSource_continuousOn (cellLength := cellLength) domain branch admissible
    (input+4) (branchGrade_large input) (continuous (input+6))
  have applied := operatorContinuous.clm_apply residualContinuous
  apply applied.congr
  intro point member
  exact (originalCompletedBranchInverse_core parameters reference inside branch domain inverse.parameterLoss
    currentInverse inverse.constant inverse.nonnegative tame grade input ordered point member
      (originalNonlinearSource parameters cellLength reference inside point (branch point))).symm

include leftLaw openDomain included low continuous in
/-- One literal original smoothed Newton step preserves all-grade parameter
continuity on the SAME fixed open parameter set. -/
theorem originalNewtonStep_continuousOn (time : ℝ) (positive : 0 < time) (grade : ℕ) :
    ContinuousOn (fun point => stateSmoothEmbedding parameters reference inside (grade+4)
      (branchGrade_large grade) (smoothedNewtonNext parameters reference inside cellLength point time
        (branch point) (inverse.map point (branch point)))) domain := by
  have inverseContinuous := inverse.appliedInverse_continuousOn leftLaw domain openDomain included branch low continuous grade
  have smoothed := originalStateSmoothing_continuousOn parameters reference inside domain
    (fun point => inverse.map point (branch point)
      (originalNonlinearSource parameters cellLength reference inside point (branch point)))
    (grade+4) (branchGrade_large grade) time positive inverseContinuous
  apply ((continuous grade).add smoothed.neg).congr
  intro point member
  let embedding := stateSmoothEmbedding parameters reference inside (grade+4) (branchGrade_large grade)
  let value := originalStateSmoothing parameters reference inside time (inverse.map point (branch point)
    (originalNonlinearSource parameters cellLength reference inside point (branch point)))
  change embedding (branch point + -value) = embedding (branch point)+ -embedding value
  exact (embedding.map_add _ _).trans (congrArg (fun output => embedding (branch point)+output) (embedding.map_neg value))

end OriginalNewtonInverse
end Grad.NashMoser.OriginalIteration
