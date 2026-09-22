import AKD5ActualConjugatedKernelFidelity
import AJL7SameKnownPhysicalResponseCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.SourceCollarCoefficients
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCurrentLow
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness
open Grad.AnnularStrongOrbit Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularKnownLow
open Grad.AnnularSmoothCore

/-- Finite radial order may take its own input reserve. Coherent inserted
curves yield smoothness of ONE fixed output curve at the original grade. -/
theorem finiteConjugatedKernelCurve_smooth {source target : ℕ} {lower : ℝ}
    {field : DivisionRow source lower} (finite : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target) (grade : ℕ)
    (regularity : ∀ order : ℕ, ∃ reserve : ℕ,
      ContDiffOn ℝ order (radialConjugatedAction parameters lower positive bounded kernel grade reserve) (Icc lower 1)) :
    ContDiffOn ℝ ∞ (fun radius => radialConjugatedAction parameters lower positive bounded kernel grade 0 radius
      (finite.conjugatedPolynomial grade radius)) (Icc lower 1) := by
  apply contDiffOn_infty.mpr
  intro order
  obtain ⟨reserve, smooth⟩ := regularity order
  have realSmooth := ((ContinuousLinearMap.restrictScalarsIsometry ℂ (CellL2 source) (CellL2 target) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn smooth
  have mapped := realSmooth.clm_apply ((contDiffOn_infty.mp
    (finite.conjugatedPolynomial_smooth positive (grade + reserve))) order)
  apply mapped.congr
  intro radius _
  exact (radialConjugatedAction_finite_reserve finite parameters positive bounded kernel grade reserve radius).symm

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (core : OriginalSmoothSourceCore parameters)

/-- SAME j, c and rV on the once-only original known source packet,
represented at the original phase-conjugated output grade. -/
def conjugatedKnownPhysicalRowCurve (row : Fin 3) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) grade 0 radius
    (conjugatedKnownSourceCurve parameters lower length positive bounded.le lengthPositive core grade radius)

theorem conjugatedKnownPhysicalRowCurve_actual (row : Fin 3) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core row grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
                (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
                  ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)))) radius mode) :=
  radialConjugatedAction_actual parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le
      ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core))) grade
    (conjugatedKnownSourceCurve parameters lower length positive bounded.le lengthPositive core grade)
    (conjugatedKnownSourceCurve_actual parameters lower length positive bounded.le lengthPositive core grade)

theorem conjugatedKnownPhysicalRowCurve_reserve (row : Fin 3) (grade reserve : ℕ) (radius : ℝ) :
    conjugatedKnownPhysicalRowCurve parameters length compact lower positive bounded lengthPositive state core row grade radius =
      radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters length compact state row) grade reserve radius
        (conjugatedKnownSourceCurve parameters lower length positive bounded.le lengthPositive core (grade + reserve) radius) :=
  (radialConjugatedAction_finite_reserve
    (smoothStrongSevenRow parameters lower length positive bounded.le lengthPositive core)
    parameters positive bounded.le (lowPhysicalRowKernel parameters length compact state row) grade reserve radius).symm

end Grad.AnnularSmoothSources
