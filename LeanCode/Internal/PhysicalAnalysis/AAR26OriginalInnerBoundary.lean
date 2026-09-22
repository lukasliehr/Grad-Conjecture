import AAR23OriginalOuterBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularEnergyTrace_eq_radial (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (endpoint : Fin 2)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive bounded lengthPositive endpoint field mode =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        weightedRadialTrace 1 lower positive bounded endpoint
          (annularModeRadialH1 lower length positive mode field) := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    (isClosed_eq
      (((lp.evalCLM ℂ (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 mode).comp
        (annularEnergyTrace lower length positive bounded lengthPositive endpoint)).continuous)
      (((weightedRadialTrace 1 lower positive bounded endpoint).continuous.comp
        (annularModeRadialH1 lower length positive mode).continuous).const_smul
          (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ))) _ field
  intro core
  change annularEnergyTrace lower length positive bounded lengthPositive endpoint
      (annularEnergyCoreInto lower length positive core) mode =
    (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
      weightedRadialTrace 1 lower positive bounded endpoint
        (annularModeRadialH1 lower length positive mode (annularEnergyCoreInto lower length positive core))
  rw [annularEnergyTrace_core, finiteAnnularTraceCore_apply,
    annularModeRadialH1_core, weightedRadialTrace_core]
  rfl

def annularPhysicalValueSection (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (mode : HighAnnularMode)
    (field : annularEnergySpace lower length positive) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (annularInversePhase parameters mode.val.2)
    (weightedRadialSection 1 lower positive bounded
      (annularModeRadialH1 lower length positive mode field))

theorem annularPhysicalValueSection_bulk (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (mode : HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    radialSectionL2 1 lower positive bounded.le
      (annularPhysicalValueSection parameters lower length positive bounded mode field) =
      annularPhysicalValue parameters lower length positive bounded.le mode field := by
  unfold annularPhysicalValueSection
  rw [radialSectionL2_scalar, weightedRadialSection_bulk]
  rfl

/-- The original inner datum is the inverse of sqrt(nu) exp(Phi(a)) d. -/
def annularInnerDatum (parameters : PhaseParameters) (lower : ℝ) (mode : HighAnnularMode)
    (normalized : ComplexEuclidean 1) : ComplexEuclidean 1 :=
  annularInversePhase parameters mode.val.2 lower •
    ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ)⁻¹ • normalized)

theorem annularPhysicalValueSection_inner (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (mode : HighAnnularMode) :
    annularPhysicalValueSection parameters lower length positive bounded mode
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
      ⟨lower, le_rfl, bounded.le⟩ = annularInnerDatum parameters lower mode (innerValue mode) := by
  let solution := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  have sharp := annularEnergyTrace_eq_radial lower length positive bounded lengthPositive 0 mode solution
  have innerLaw := congrArg (fun value : AnnularBoundary => value mode)
    (annularVariationalSolution_inner parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
  have traceLaw := sharp.symm.trans innerLaw
  have nonzero : (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (zero_lt_one.trans_le (annularFrequency_one_le _ _))).ne'
  have normalized := congrArg (fun vector : ComplexEuclidean 1 =>
    (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ)⁻¹ • vector) traceLaw
  rw [smul_smul, inv_mul_cancel₀ nonzero, one_smul] at normalized
  have endpoint := weightedRadialSection_endpoint 1 lower positive bounded 0
    (annularModeRadialH1 lower length positive mode solution)
  change weightedRadialSection 1 lower positive bounded
    (annularModeRadialH1 lower length positive mode solution) ⟨lower, le_rfl, bounded.le⟩ = _ at endpoint
  change annularInversePhase parameters mode.val.2 lower •
    weightedRadialSection 1 lower positive bounded
      (annularModeRadialH1 lower length positive mode solution) ⟨lower, le_rfl, bounded.le⟩ = _
  rw [endpoint, normalized]
  rfl

end Grad.AnnularReconstruction
