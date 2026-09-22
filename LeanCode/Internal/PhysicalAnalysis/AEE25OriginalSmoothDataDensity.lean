import AEE24ActualContinuousDataRange

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

def scalarCoordinateCurve (curve : C(ℝ, ComplexEuclidean 1)) : C(ℝ, ℂ) :=
  ⟨fun radius => curve radius 0,
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp curve.continuous⟩

theorem scalarOne_coordinate (value : ComplexEuclidean 1) : scalarOne (value 0) = value := by
  apply PiLp.ext
  intro index
  fin_cases index
  exact scalarOne_apply_zero _

theorem scalarOneCurve_coordinate (curve : C(ℝ, ComplexEuclidean 1)) :
    scalarOneCurve (scalarCoordinateCurve curve) = curve := by
  apply ContinuousMap.ext
  intro radius
  exact scalarOne_coordinate _

theorem scalarOneCurve_zero : scalarOneCurve 0 = 0 := by
  apply ContinuousMap.ext
  intro radius
  exact map_zero scalarOne

theorem lowScalarStoredCurve_zero (lower : ℝ) (positive : 0 < lower) :
    lowScalarStoredCurve lower positive 0 = 0 := by
  unfold lowScalarStoredCurve
  rw [scalarOneCurve_zero, map_zero, map_zero]

/-- Original rho-L2 source density; the fixed-collar storage map is an
actual isomorphism and does not alter the analytic weight. -/
def lowSmoothStoredSource (lower : ℝ) (positive : 0 < lower) :
    SmoothRadialCore 1 →ₗ[ℝ] CollarL2 (ComplexEuclidean 1) lower :=
  ((collarScalar 1 lower (lowStorageWeight lower positive)).restrictScalars ℝ).toLinearMap.comp
    (smoothRadialValueL2 1 lower)

theorem lowSmoothStoredSource_denseRange (lower : ℝ) (positive : 0 < lower) :
    DenseRange (lowSmoothStoredSource lower positive) := by
  have onto : Function.Surjective (collarScalar 1 lower (lowStorageWeight lower positive)) :=
    fun field => ⟨collarScalar 1 lower (lowStorageInverse lower positive) field,
      lowStorage_encode_decode lower positive field⟩
  exact onto.denseRange.comp (smoothRadialValueL2_denseRange 1 lower)
    (collarScalar 1 lower (lowStorageWeight lower positive)).continuous

theorem lowSmoothStoredSource_actual (lower : ℝ) (positive : 0 < lower) (core : SmoothRadialCore 1) :
    lowSmoothStoredSource lower positive core =
      lowScalarStoredCurve lower positive (scalarCoordinateCurve core.val.val.1) := by
  unfold lowScalarStoredCurve
  rw [scalarOneCurve_coordinate]
  rfl

def lowBulkDataInjection (lower : ℝ) : LowEnergyBulk lower →L[ℂ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ _ _)

def lowBoundaryDataInjection (lower : ℝ) : LowEnergyBoundary →L[ℂ] LowEnergyData lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℂ _ _)

def lowBulkSingleData (lower : ℝ) (index : LowAnnularIndex) :
    CollarL2 (ComplexEuclidean 1) lower →L[ℂ] LowEnergyData lower :=
  (lowBulkDataInjection lower).comp (lp.singleContinuousLinearMap ℂ (fun _ : LowAnnularIndex => CollarL2 (ComplexEuclidean 1) lower) 2 index)

def lowBoundarySingleData (lower : ℝ) (index : LowAnnularIndex) :
    ComplexEuclidean 1 →L[ℂ] LowEnergyData lower :=
  (lowBoundaryDataInjection lower).comp (lp.singleContinuousLinearMap ℂ (fun _ : LowAnnularIndex => ComplexEuclidean 1) 2 index)

end Grad.AnnularLowCompletion
