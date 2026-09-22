import AKCZ9DirectParameterBranchBootstrap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 3500
open Set
open scoped ContDiff
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds Grad.SmoothForward
open Grad.NashMoser.OriginalLimit

variable (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference insideR)

/-- The original finite parameter and constrained state branch in the SAME
mixed completed grade. -/
theorem originalMixedBranch_contDiffOn (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ∞ω) (domain : Set OriginalFiniteParameter)
    (smooth : ContDiffOn ℝ order (fun point => stateSmoothEmbedding parameters reference insideR grade large (branch point)) domain) :
    ContDiffOn ℝ order (fun point => realMixedCoreEmbed parameters reference insideR grade large
      (point.1,point.2,branch point)) domain := by
  change ContDiffOn ℝ order (fun point : OriginalFiniteParameter =>
    WithLp.toLp 1 (WithLp.toLp 1 point.1,WithLp.toLp 1
      (point.2,stateSmoothEmbedding parameters reference insideR grade large (branch point)))) domain
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR grade large) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR grade large) := inferInstance
  have seedSmooth := seedL1Equiv.symm.contDiff.comp_contDiffOn (contDiffOn_fst : ContDiffOn ℝ order (fun point : OriginalFiniteParameter => point.1) domain)
  have jointSmooth := (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ
    (stateRange parameters reference insideR grade large)).symm.contDiff.comp_contDiffOn
      ((contDiffOn_snd : ContDiffOn ℝ order (fun point : OriginalFiniteParameter => point.2) domain).prodMk smooth)
  exact (WithLp.prodContinuousLinearEquiv 1 ℝ SeedL1
    (RealJointAmbient parameters reference insideR grade large)).symm.contDiff.comp_contDiffOn
      (seedSmooth.prodMk jointSmooth)

/-- The actual completed finite-parameter source derivative. -/
def originalBranchParameterDerivative (grade : ℕ) (large : 3 ≤ grade)
    (point : OriginalFiniteParameter) : OriginalFiniteParameter →L[ℝ] sourceRange parameters grade large :=
  (fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
    (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade)
      (point.1,point.2,branch point))).comp
        (originalFiniteDirectionCompleted parameters reference insideR (grade+6) (realHighLarge grade))

/-- The original state derivative realized through the same mixed residual. -/
def originalBranchForward (grade : ℕ) (large : 3 ≤ grade)
    (point : OriginalFiniteParameter) : stateRange parameters reference insideR (grade+6) (realHighLarge grade) →L[ℝ]
      sourceRange parameters grade large :=
  (fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large)
    (realMixedCoreEmbed parameters reference insideR (grade+6) (realHighLarge grade)
      (point.1,point.2,branch point))).comp
        (physicalStateDirection parameters reference insideR (grade+6) (realHighLarge grade))

/-- QYP's established smoothness supplies every finite-order forward factor
from only that finite-order regularity of the branch in its original grade. -/
theorem originalBranch_derivativeFactors_contDiffOn (grade : ℕ) (large : 3 ≤ grade)
    (order : ℕ) (domain : Set OriginalFiniteParameter)
    (admissible : ∀ point ∈ domain, point.1 ∈ Seed.parameterDomain ∧
      ChartAxisCondition (smoothingChartCore parameters (branch point).val))
    (smooth : ContDiffOn ℝ order (fun point => stateSmoothEmbedding parameters reference insideR
      (grade+6) (realHighLarge grade) (branch point)) domain) :
    ContDiffOn ℝ order (originalBranchForward parameters cellLength reference insideR branch grade large) domain ∧
    ContDiffOn ℝ order (originalBranchParameterDerivative parameters cellLength reference insideR branch grade large) domain := by
  let : NormedSpace ℝ (RealJointAmbient parameters reference insideR (grade+6) (realHighLarge grade)) := inferInstance
  let : NormedSpace ℝ (RealMixedAmbient parameters reference insideR (grade+6) (realHighLarge grade)) := inferInstance
  have mixedSmooth := originalMixedBranch_contDiffOn parameters reference insideR branch (grade+6)
    (realHighLarge grade) (order : ℕ∞ω) domain smooth
  have derivativeSmooth : ContDiffOn ℝ order
      (fderiv ℝ (completedRealPhysicalMixedSlice parameters cellLength reference insideR grade large))
      (realMixedDomain parameters reference insideR (grade+6) (realHighLarge grade)) :=
    (completedRealPhysicalMixedSlice_contDiffOn parameters cellLength reference insideR grade large).fderiv_of_isOpen
      (realMixedDomain_isOpen parameters reference insideR (grade+6) (realHighLarge grade))
      (by exact_mod_cast (le_top : ((order+1 : ℕ) : ℕ∞) ≤ ⊤))
  have composed := derivativeSmooth.comp mixedSmooth (fun point member =>
    (realMixedDomain_core_iff parameters reference insideR (grade+6) (realHighLarge grade)
      (point.1,point.2,branch point)).mpr (admissible point member))
  exact ⟨composed.clm_comp contDiffOn_const,composed.clm_comp contDiffOn_const⟩

theorem originalBranchForward_original (grade : ℕ) (large : 4 ≤ grade)
    (point : OriginalFiniteParameter) (insideS : point.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters (branch point).val)) :
    originalBranchForward parameters cellLength reference insideR branch grade (forwardLarge large) point =
      actualPhysicalSmoothForward parameters cellLength reference insideR point.1 grade large (point.2,branch point) := by
  rw [actualPhysicalSmoothForward_mixed parameters cellLength reference insideR point.1 insideS grade large
    (point.2,branch point) axis]
  rfl

theorem originalBranchParameterDerivative_core (grade : ℕ) (large : 3 ≤ grade)
    (point : OriginalFiniteParameter) (insideS : point.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters (branch point).val)) (direction : OriginalFiniteParameter) :
    originalBranchParameterDerivative parameters cellLength reference insideR branch grade large point direction =
      sourceSmoothEmbedding parameters grade large
        (originalParameterDerivative parameters reference insideR cellLength (point.1,point.2,branch point) insideS axis direction) :=
  (originalParameterDerivative_completed parameters reference insideR cellLength (point.1,point.2,branch point)
    insideS axis grade large direction).symm

end Grad.NashMoser.InverseCalculus
