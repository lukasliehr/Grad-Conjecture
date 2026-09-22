import AEE22ActualModalResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowScalarStoredCurve (lower : ℝ) (positive : 0 < lower) (curve : C(ℝ, ℂ)) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (lowStorageWeight lower positive)
    (collarContinuousL2 (ComplexEuclidean 1) lower (scalarOneCurve curve))

/-- Literal finite continuous residuals and literal weighted incoming data. -/
def lowPairContinuousData (lower length : ℝ) (positive : 0 < lower) (mode : LowAnnularMode)
    (first second : C(ℝ, ℂ)) (initialFirst initialSecond : ℂ) : LowEnergyData lower :=
  WithLp.toLp 2 (
    (lp.single 2 (0, mode) (lowScalarStoredCurve lower positive first) : LowEnergyBulk lower) +
      lp.single 2 (1, mode) (lowScalarStoredCurve lower positive second),
    (lp.single 2 (0, mode) (lowIncomingFactor lower length mode • scalarOne initialFirst) : LowEnergyBoundary) +
      lp.single 2 (1, mode) (lowIncomingFactor lower length mode • scalarOne initialSecond))

theorem lowPairLp_apply {E : Type*} [NormedAddCommGroup E] (first second : E)
    (mode other : LowAnnularMode) (row : Fin 2) :
    ((lp.single 2 (0, mode) first : lp (fun _ : LowAnnularIndex => E) 2) + (lp.single 2 (1, mode) second : lp (fun _ : LowAnnularIndex => E) 2)) (row, other) =
      if other = mode then if row = 0 then first else second else 0 := by
  rw [lp.coeFn_add, Pi.add_apply]
  simp only [lp.single_apply, Pi.single_apply]
  fin_cases row <;> by_cases same : other = mode <;> simp [same]

theorem lowPairContinuousData_residual_ae (lower length : ℝ) (positive : 0 < lower) (mode : LowAnnularMode)
    (first second : C(ℝ, ℂ)) (initialFirst initialSecond : ℂ) (row : Fin 2) (other : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowDataResidual lower positive (lowPairContinuousData lower length positive mode first second initialFirst initialSecond)
        (row, other) radius =
        if other = mode then scalarOne (if row = 0 then first radius else second radius) else 0 := by
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1),
    collarScalar 1 lower (lowStorageInverse lower positive)
      (((lp.single 2 (0, mode) (lowScalarStoredCurve lower positive first) : LowEnergyBulk lower) +
        (lp.single 2 (1, mode) (lowScalarStoredCurve lower positive second) : LowEnergyBulk lower)) (row, other)) radius = _
  rw [lowPairLp_apply]
  by_cases same : other = mode
  · subst other
    have rowCases : row = 0 ∨ row = 1 := by omega
    rcases rowCases with rfl | rfl
    · simp only [ite_true, lowScalarStoredCurve, lowStorage_decode_encode]
      exact (collarContinuous_memLp (ComplexEuclidean 1) lower (scalarOneCurve first)).coeFn_toLp
    · simp only [Fin.reduceEq, ite_true, ite_false, lowScalarStoredCurve, lowStorage_decode_encode]
      exact (collarContinuous_memLp (ComplexEuclidean 1) lower (scalarOneCurve second)).coeFn_toLp
  · simp only [same, if_false, map_zero]
    exact Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))

theorem lowPairContinuousData_incoming (lower length : ℝ) (positive : 0 < lower) (mode : LowAnnularMode)
    (first second : C(ℝ, ℂ)) (initialFirst initialSecond : ℂ) (row : Fin 2) (other : LowAnnularMode) :
    (lowPairContinuousData lower length positive mode first second initialFirst initialSecond).ofLp.2 (row, other) =
      if other = mode then lowIncomingFactor lower length mode •
        scalarOne (if row = 0 then initialFirst else initialSecond) else 0 := by
  change ((lp.single 2 (0, mode) (lowIncomingFactor lower length mode • scalarOne initialFirst) : LowEnergyBoundary) +
      (lp.single 2 (1, mode) (lowIncomingFactor lower length mode • scalarOne initialSecond) : LowEnergyBoundary)) (row, other) = _
  rw [lowPairLp_apply]
  split_ifs <;> rfl

end Grad.AnnularLowCompletion
