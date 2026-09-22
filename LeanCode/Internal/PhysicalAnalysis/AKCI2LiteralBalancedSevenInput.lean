import AKCI1ActualPhysicalRowTameAction
import AKF1ExactConjugatedUnknownInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularSmoothCore Grad.AnnularWeightedSystem Grad.BoundaryLift Grad.GaugeCoefficients.Physical.Ledger

/-- SR14's balanced coordinates are (nu*Xi/r,x). This is exactly the
homogeneous original seven packet (x,RXi/r,Xi_zeta,Xi/r,0,0,0). -/
def balancedSevenInput (parameters : PhaseParameters) (radius : ℝ) :
    PhysicalHilbertPair →L[ℂ] CellL2 7 :=
  let first := ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)
  let second := ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)
  ((hilbertSlotInjection parameters 0).comp second +
    (hilbertSlotInjection parameters 1).comp ((hilbertFrequencyOperator parameters 1 (some false)).comp first)) +
    (radius : ℂ) • (hilbertSlotInjection parameters 2).comp ((hilbertFrequencyOperator parameters 1 (some true)).comp first) +
    (hilbertSlotInjection parameters 3).comp ((hilbertFrequencyOperator parameters 1 none).comp first)

def balancedSevenPointMap (radius : ℝ) (mode : ℤ × ℤ) :
    (ComplexEuclidean 1 × ComplexEuclidean 1) →L[ℂ] ComplexEuclidean 7 :=
  let first := ContinuousLinearMap.fst ℂ (ComplexEuclidean 1) (ComplexEuclidean 1)
  let second := ContinuousLinearMap.snd ℂ (ComplexEuclidean 1) (ComplexEuclidean 1)
  ((matrixUnit (0 : Fin 7) (0 : Fin 1)).comp second +
    (matrixUnit (1 : Fin 7) (0 : Fin 1)).comp (frequencyRatioSymbol (some false) mode • first)) +
    (radius : ℂ) • (matrixUnit (2 : Fin 7) (0 : Fin 1)).comp (frequencyRatioSymbol (some true) mode • first) +
    (matrixUnit (3 : Fin 7) (0 : Fin 1)).comp (frequencyRatioSymbol none mode • first)

theorem balancedSevenInput_point (parameters : PhaseParameters) (radius : ℝ)
    (field : PhysicalHilbertPair) (mode : ℤ × ℤ) :
    balancedSevenInput parameters radius field mode =
      balancedSevenPointMap radius mode (hilbertPairCoefficient mode field) := rfl

theorem balancedSevenInput_sameGrade (parameters : PhaseParameters) (radius : ℝ)
    (grade : ℕ) (high low : PhysicalHilbertPair)
    (same : ∀ mode, hilbertPairCoefficient mode high =
      (annularFrequency mode.1 mode.2 : ℂ)^grade • hilbertPairCoefficient mode low) :
    ∀ mode, balancedSevenInput parameters radius high mode =
      (annularFrequency mode.1 mode.2 : ℂ)^grade • balancedSevenInput parameters radius low mode := by
  intro mode
  rw [balancedSevenInput_point,balancedSevenInput_point,same]
  exact (balancedSevenPointMap radius mode).map_smul _ _

theorem balancedSevenPointMap_physical (radius : ℝ) (nonzero : radius ≠ 0)
    (mode : ℤ × ℤ) (x xi : ComplexEuclidean 1) :
    balancedSevenPointMap radius mode
      (((annularFrequency mode.1 mode.2 : ℂ)/(radius : ℂ)) • xi,x) =
      rawPhysicalSevenVector radius mode x xi := by
  have frequencyNonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
  have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  change (((matrixUnit (0 : Fin 7) (0 : Fin 1)) x +
    (matrixUnit (1 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol (some false) mode •
      (((annularFrequency mode.1 mode.2 : ℂ)/(radius : ℂ)) • xi))) +
    (radius : ℂ) • (matrixUnit (2 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol (some true) mode •
      (((annularFrequency mode.1 mode.2 : ℂ)/(radius : ℂ)) • xi))) +
    (matrixUnit (3 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol none mode •
      (((annularFrequency mode.1 mode.2 : ℂ)/(radius : ℂ)) • xi)) = _
  apply PiLp.ext
  intro slot
  simp only [rawPhysicalSevenVector,map_smul,smul_smul,PiLp.add_apply,PiLp.smul_apply,
    smul_eq_mul,frequencyRatioSymbol,frequencyNumerator]
  field_simp

end Grad.OriginalCartesianTameEstimate
