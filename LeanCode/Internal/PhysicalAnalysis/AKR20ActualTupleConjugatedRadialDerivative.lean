import AKR19GenuineTupleConjugatedPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularVariational

variable (parameters : PhaseParameters) (lower : ℝ) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower)

theorem tupleWeightedCurve_shift (slot : Fin 4) (grade reserve : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    tupleWeightedCurve parameters lower tuple slot (grade+reserve) radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ)^reserve •
        tupleWeightedCurve parameters lower tuple slot grade radius mode := by
  rw [tupleWeightedCurve_coefficient parameters lower tuple slot (grade+reserve) radius inside,
    tupleWeightedCurve_coefficient parameters lower tuple slot grade radius inside,pow_add,Complex.ofReal_mul,smul_smul]
  simp only [Complex.ofReal_pow,smul_smul]
  congr 1
  ring

def tuplePhaseSlopeCurve (slot : Fin 4) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  phaseSlopeDiagonal parameters 1 5 radius (tupleWeightedCurve parameters lower tuple slot (grade+5) radius)

include bounded in
theorem tuplePhaseSlopeCurve_continuous (slot : Fin 4) (grade : ℕ) :
    ContinuousOn (tuplePhaseSlopeCurve parameters lower tuple slot grade) (Icc lower 1) := by
  have operator := (phaseSlopeDiagonal_contDiffOn parameters 1 5 0 (by norm_num) lower 1 bounded).continuousOn
  exact (((ContinuousLinearMap.apply ℂ (CellL2 1)).flip.bilinearRestrictScalars ℝ).isBoundedBilinearMap.continuous.comp_continuousOn
    (operator.prodMk (tupleWeightedCurve_smooth parameters lower tuple slot (grade+5)).continuousOn))

theorem tuplePhaseSlopeCurve_coefficient (slot : Fin 4) (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    tuplePhaseSlopeCurve parameters lower tuple slot grade radius mode =
      (annularPhaseSlope parameters mode.2 radius : ℂ) • tupleWeightedCurve parameters lower tuple slot grade radius mode :=
  phaseSlopeDiagonal_same parameters 1 5 (by norm_num) radius _ _
    (tupleWeightedCurve_shift parameters lower tuple slot grade 5 radius inside) mode

/-- This is the actual phase-weighted derivative of the tuple field. -/
def tupleConjugatedDerivativeCurve (slot : Fin 4) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  derivWithin (tupleWeightedCurve parameters lower tuple slot grade) (Icc lower 1) radius -
    tuplePhaseSlopeCurve parameters lower tuple slot grade radius

include bounded in
theorem tupleConjugatedDerivativeCurve_continuous (slot : Fin 4) (grade : ℕ) :
    ContinuousOn (tupleConjugatedDerivativeCurve parameters lower tuple slot grade) (Icc lower 1) :=
  ((tupleWeightedCurve_smooth parameters lower tuple slot grade).continuousOn_derivWithin
    (uniqueDiffOn_Icc bounded) (by simp)).sub (tuplePhaseSlopeCurve_continuous parameters lower bounded tuple slot grade)

include bounded in
theorem tupleConjugatedDerivativeCurve_coefficient (slot : Fin 4) (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    tupleConjugatedDerivativeCurve parameters lower tuple slot grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          derivWithin (fun point => originalPhysicalCoefficient (tuple.val slot) point mode) (Icc lower 1) radius) := by
  have physical := ((originalTuple_coefficient_smooth parameters lower tuple slot mode).differentiableOn (by simp) radius inside).hasDerivWithinAt
  have phase := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt radius (radialPhase_hasDerivAt parameters mode.2 radius).exp
  have product := (phase.hasDerivWithinAt (s := Icc lower 1)).smul physical
  have weighted := product.const_smul ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ)
  have actual := weighted.congr (tupleWeightedCurve_coefficient parameters lower tuple slot grade · · mode)
    (tupleWeightedCurve_coefficient parameters lower tuple slot grade radius inside mode)
  have coordinate := radialJet_map lower bounded (tupleWeightedCurve parameters lower tuple slot grade)
    (tupleWeightedCurve_smooth parameters lower tuple slot grade)
    ((lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode)) 1 radius inside
  simp only [iteratedDerivWithin_one] at coordinate
  change derivWithin (fun point => tupleWeightedCurve parameters lower tuple slot grade point mode) (Icc lower 1) radius =
    derivWithin (tupleWeightedCurve parameters lower tuple slot grade) (Icc lower 1) radius mode at coordinate
  have value := actual.derivWithin (uniqueDiffOn_Icc bounded radius inside)
  change derivWithin (tupleWeightedCurve parameters lower tuple slot grade) (Icc lower 1) radius mode -
    tuplePhaseSlopeCurve parameters lower tuple slot grade radius mode = _
  rw [← coordinate,value,tuplePhaseSlopeCurve_coefficient parameters lower tuple slot grade radius inside mode,
    tupleWeightedCurve_coefficient parameters lower tuple slot grade radius inside mode]
  ext component
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,Complex.ofRealCLM_apply,
    Complex.ofReal_mul,Function.comp_apply]
  ring

end Grad.AnnularOriginalCoreRealization
