import AKF11ActualSourceSmoothnessAssembly
import AKC3ConjugatedGradeCoherence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSmoothCore Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2 Grad.BoundaryKernelAction

theorem radialConjugatedAction_addReserve {source target : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (grade first second : ℕ) (radius : ℝ) :
    radialConjugatedAction parameters lower positive bounded kernel grade (first + second) radius =
      (radialConjugatedAction parameters lower positive bounded kernel grade first radius).comp
        (hilbertReserve parameters source second) := by
  apply ContinuousLinearMap.ext
  intro field
  change bulkKernelAction parameters grade _ _ (hilbertReserve parameters source (first + second) field) =
    bulkKernelAction parameters grade _ _ (hilbertReserve parameters source first
      (hilbertReserve parameters source second field))
  rw [hilbertReserve_add]
  rfl

theorem radialConjugatedAction_smooth_largerReserve {source target : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (grade smaller larger order : ℕ) (ordered : smaller ≤ larger)
    (smooth : ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive bounded kernel grade smaller) (Icc lower 1)) :
    ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive bounded kernel grade larger) (Icc lower 1) := by
  have composed := finiteOrderOperatorComposition smooth
    (show ContDiffOn ℝ order (fun _ : ℝ => hilbertReserve parameters source (larger - smaller)) (Icc lower 1)
      from contDiffOn_const)
  apply composed.congr
  intro radius _
  simpa only [Nat.add_sub_of_le ordered] using
    radialConjugatedAction_addReserve parameters lower positive bounded kernel grade smaller (larger - smaller) radius

/-- Three independently proved row orders can use one finite reserve that
also meets the phase-slope requirement. No analytic width is changed. -/
theorem originalRows_commonReserve (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact) (grade order minimum : ℕ)
    (regularity : ∀ index : Fin 3, ∃ reserve : ℕ, ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive bounded
        (lowPhysicalRowKernel parameters length compact state index) grade reserve) (Icc lower 1)) :
    ∃ reserve : ℕ, minimum ≤ reserve ∧ ∀ index : Fin 3, ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive bounded
        (lowPhysicalRowKernel parameters length compact state index) grade reserve) (Icc lower 1) := by
  obtain ⟨first, firstSmooth⟩ := regularity 0
  obtain ⟨second, secondSmooth⟩ := regularity 1
  obtain ⟨third, thirdSmooth⟩ := regularity 2
  refine ⟨first + second + third + minimum, by omega, ?_⟩
  intro index
  fin_cases index
  · exact radialConjugatedAction_smooth_largerReserve parameters lower positive bounded
      (lowPhysicalRowKernel parameters length compact state 0) grade first _ order (by omega) firstSmooth
  · exact radialConjugatedAction_smooth_largerReserve parameters lower positive bounded
      (lowPhysicalRowKernel parameters length compact state 1) grade second _ order (by omega) secondSmooth
  · exact radialConjugatedAction_smooth_largerReserve parameters lower positive bounded
      (lowPhysicalRowKernel parameters length compact state 2) grade third _ order (by omega) thirdSmooth

end Grad.AnnularWeightedSystem
