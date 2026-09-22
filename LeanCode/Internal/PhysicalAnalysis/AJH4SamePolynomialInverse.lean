import AJH3ReuseOriginalKernelAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.BoundaryLift

theorem polynomialObservation_ext {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (first second : CellL2 source →L[ℂ] CellL2 target)
    (same : ∀ field, first (polynomialObservation parameters power source field) =
      second (polynomialObservation parameters power source field)) : first = second := by
  apply ContinuousLinearMap.ext
  have equality := (polynomialObservation_denseRange parameters power source).equalizer first.continuous second.continuous (funext same)
  exact fun field => congrFun equality field

theorem polynomialKernelAction_identity (parameters : PhaseParameters) (power dimension : ℕ) :
    polynomialKernelAction parameters power (fullIdentityKernel parameters dimension) = ContinuousLinearMap.id ℂ (CellL2 dimension) := by
  apply polynomialObservation_ext parameters power
  intro field
  rw [← polynomialObservation_kernel, fullNegativeKernelAction_identity]
  rfl

theorem polynomialKernelAction_add {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (first second : FullTwoFrequencyKernel parameters source target) :
    polynomialKernelAction parameters power (fullKernelAdd first second) =
      polynomialKernelAction parameters power first + polynomialKernelAction parameters power second := by
  apply polynomialObservation_ext parameters power
  intro field
  rw [← polynomialObservation_kernel, fullNegativeKernelAction_add, map_add,
    polynomialObservation_kernel, polynomialObservation_kernel]
  rfl

theorem polynomialKernelAction_sub {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (first second : FullTwoFrequencyKernel parameters source target) :
    polynomialKernelAction parameters power (fullKernelSub first second) =
      polynomialKernelAction parameters power first - polynomialKernelAction parameters power second := by
  apply polynomialObservation_ext parameters power
  intro field
  rw [← polynomialObservation_kernel, fullNegativeKernelAction_sub, map_sub,
    polynomialObservation_kernel, polynomialObservation_kernel]
  rfl

theorem polynomialKernelAction_neg {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (kernel : FullTwoFrequencyKernel parameters source target) :
    polynomialKernelAction parameters power (fullKernelNeg kernel) = -polynomialKernelAction parameters power kernel := by
  apply polynomialObservation_ext parameters power
  intro field
  rw [← polynomialObservation_kernel, fullNegativeKernelAction_neg, map_neg, polynomialObservation_kernel]
  rfl

/-- Both exact inverse laws are transported from the accepted original kernel
inverse, at every polynomial grade; higher-grade smallness is not needed. -/
theorem polynomialKernelAction_inverse {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (kernel : FullTwoFrequencyKernel parameters dimension dimension) (low : ℝ)
    (bounded : fullKernelMoment parameters 0 kernel ≤ low) (small : low < 1) :
    let forward := polynomialKernelAction parameters power (fullKernelNegativeIdentityPerturbation parameters kernel)
    let inverse := polynomialKernelAction parameters power (fullKernelNegativeIdentityInverse parameters kernel low bounded small)
    forward.comp inverse = ContinuousLinearMap.id ℂ (CellL2 dimension) ∧
      inverse.comp forward = ContinuousLinearMap.id ℂ (CellL2 dimension) := by
  dsimp only
  constructor
  · rw [← polynomialKernelAction_comp, fullKernelNegativeIdentity_inverse_right, polynomialKernelAction_identity]
  · rw [← polynomialKernelAction_comp, fullKernelNegativeIdentity_inverse_left, polynomialKernelAction_identity]

/-- The original entry family determines the polynomial operator even when
its bookkeeping phase varies with the radius. -/
theorem polynomialKernelAction_congr {source target : ℕ} (firstParameters secondParameters : PhaseParameters)
    (power : ℕ) (first : FullTwoFrequencyKernel firstParameters source target)
    (second : FullTwoFrequencyKernel secondParameters source target) (same : SameKernelEntries first second) :
    polynomialKernelAction firstParameters power first = polynomialKernelAction secondParameters power second := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  apply (polynomialKernelAction_coefficient firstParameters power first field mode).unique
  exact (polynomialKernelAction_coefficient secondParameters power second field mode).congr_fun
    (fun shift => by rw [same shift (twoFrequencyTranslation shift mode)])

section InverseSmoothness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- Genuine smoothness of the SAME two-sided inverse on a closed collar.
Only the forward map is required to have an existing smoothness proof. -/
theorem sameEndomorphismInverse_contDiffOn (domain : Set ℝ)
    (forward inverse : ℝ → E →L[ℂ] E)
    (right : ∀ point ∈ domain, (forward point).comp (inverse point) = ContinuousLinearMap.id ℂ E)
    (left : ∀ point ∈ domain, (inverse point).comp (forward point) = ContinuousLinearMap.id ℂ E)
    (smooth : ContDiffOn ℝ ∞ forward domain) : ContDiffOn ℝ ∞ inverse domain := by
  let unit (point : ℝ) (inside : point ∈ domain) : (E →L[ℂ] E)ˣ :=
    ⟨forward point, inverse point, right point inside, left point inside⟩
  have smoothRing : ContDiffOn ℝ ∞ (fun point => Ring.inverse (forward point)) domain := by
    intro point inside
    have ringSmooth := (contDiffAt_ringInverse ℂ (n := ∞) (unit point inside)).restrict_scalars ℝ
    change ContDiffAt ℝ ∞ Ring.inverse (forward point) at ringSmooth
    exact ringSmooth.comp_contDiffWithinAt point (smooth point inside)
  apply smoothRing.congr
  intro point inside
  exact (Ring.inverse_unit (unit point inside)).symm

end InverseSmoothness
end Grad.AnnularRadialSmoothness
