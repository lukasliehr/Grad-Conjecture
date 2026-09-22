import AKV4GeneralOriginalHomogeneousFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2
open Grad.AnnularOriginalCoreRealization

/-- All-grade radial representatives of the actual independent source packet.
Every equality is to the prescribed datum at its original analytic phase.
This is a generic adapter contract; actual source membership is proved separately. -/
structure ActualSourceRadialCurves (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0) where
  seven : ℕ → ℝ → CellL2 7
  force : ℕ → ℝ → CellL2 1
  third : ℕ → ℝ → CellL2 1
  sevenSmooth : ∀ grade, ContDiffOn ℝ ∞ (seven grade) (Icc lower 1)
  forceSmooth : ∀ grade, ContDiffOn ℝ ∞ (force grade) (Icc lower 1)
  thirdSmooth : ∀ grade, ContDiffOn ℝ ∞ (third grade) (Icc lower 1)
  sevenSame : ∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
    seven grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        lowRhoPhysicalCoefficient parameters lower positive
          (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data)) radius mode)
  forceSame : ∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
    force grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        lowRhoPhysicalCoefficient parameters lower positive
          (strongKnownBulk parameters lower positive bounded.le data 3) radius mode)
  thirdSame : ∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
    third grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        radius • lowRhoPhysicalCoefficient parameters lower positive
          (strongToLow parameters lower positive bounded.le 0 0 data).ofLp.1.ofLp.2 radius mode)

theorem actualWeightedCurve_shift {dimension : ℕ}
    (lower : ℝ) (bounded : lower < 1) (curve : ℕ → ℝ → CellL2 dimension)
    (continuous : ∀ grade, ContinuousOn (curve grade) (Icc lower 1))
    (physical : ℝ → (ℤ × ℤ) → ComplexEuclidean dimension)
    (same : ∀ grade, ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      curve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • physical radius mode)
    (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curve (grade+reserve) radius mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve • curve grade radius mode := by
  apply collarCurve_eq_of_ae lower bounded
    (fun point => curve (grade+reserve) point mode)
    (fun point => (annularFrequency mode.1 mode.2 : ℂ)^reserve • curve grade point mode)
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_continuousOn (continuous _))
    (((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_continuousOn
      (continuous grade)).const_smul ((annularFrequency mode.1 mode.2 : ℂ)^reserve))
    ?_ inside
  filter_upwards [same (grade+reserve), same grade] with point high low
  rw [high mode,low mode,pow_add,mul_smul]
  exact smul_comm _ _ _

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)

def generalConjugatedKnownRowCurve (row : Fin 3) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) grade 0 radius (curves.seven grade radius)

theorem generalConjugatedKnownRowCurve_smooth (row : Fin 3) (grade : ℕ) :
    ContDiffOn ℝ ∞ (generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves row grade)
      (Icc lower 1) :=
  coherentConjugatedKernelCurve_smooth parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) curves.seven curves.sevenSmooth
    (actualWeightedCurve_shift lower bounded curves.seven (fun grade => (curves.sevenSmooth grade).continuousOn)
      _ curves.sevenSame) grade
    (originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive bounded row grade)

theorem generalConjugatedKnownRowCurve_actual (row : Fin 3) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves row grade radius mode =
        (annularFrequency mode.1 mode.2 : ℂ)^grade •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
                (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data))) radius mode) := by
  exact radialConjugatedAction_actual parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data)) grade
    (curves.seven grade) (by simpa only [Complex.ofReal_pow, Grad.SourceCollarDivision.annularFrequency, Grad.AnnularVariational.annularFrequency] using curves.sevenSame grade)

end Grad.AnnularGeneralSourceRegularity
