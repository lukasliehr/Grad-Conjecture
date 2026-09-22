import AAR15ActualFluxMomentWeak
import AAR16WeakRadiusDivision
import ASG30CompactWeakGraphConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarScalar_inverseRadius_radius (lower : ℝ) (positive : 0 < lower)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularInverseRadiusCurve lower positive)
      (collarScalar 1 lower annularRadiusCurve field) = field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive)
    (collarScalar 1 lower annularRadiusCurve field),
    collarScalar_ae 1 lower annularRadiusCurve field, ae_restrict_mem measurableSet_Icc]
    with radius outer inner inside
  rw [outer, inner, smul_smul]
  change ((1 / max lower radius) * radius) • field radius = field radius
  rw [max_eq_right inside.1, one_div, inv_mul_cancel₀ (positive.trans_le inside.1).ne', one_smul]

theorem annularRadialMoment_divide (lower : ℝ) (positive : 0 < lower) (field : RadialL2 1 lower) :
    collarScalar 1 lower (annularInverseRadiusCurve lower positive)
      (annularRadialMoment lower positive field) = radialOrdinary 1 lower positive field :=
  collarScalar_inverseRadius_radius lower positive _

theorem collarWeakDerivative_complex_smul (lower : ℝ) (scalar : ℂ)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    CollarWeakDerivative lower (scalar • value) (scalar • derivative) := by
  intro test vector
  rw [collarPairing_complex_smul, collarPairing_complex_smul, weak test vector, mul_neg]

section Flux
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularNormalizedQSlope (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (annularInverseRadiusSlope lower positive)
    (annularRadialMoment lower positive
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)) +
  collarScalar 1 lower (annularInverseRadiusCurve lower positive)
    (annularFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode)

theorem annularNormalizedQ_weak (bounded : lower < 1)
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (mode : HighAnnularMode) :
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    CollarWeakDerivative lower
      (radialOrdinary 1 lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode))
      (annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode) := by
  dsimp only
  have moment := annularRecoveredQ_moment_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode
  have divided := compactWeakDerivative_divide_radius lower positive _ _ moment
  rw [annularRadialMoment_divide] at divided
  exact (compactWeak_iff_collarWeak 1 lower positive bounded _ _).mp divided

def annularPhysicalQSlope (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (annularInversePhaseSlope parameters mode.val.2)
    (radialOrdinary 1 lower positive
      (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)) +
  collarScalar 1 lower (annularInversePhase parameters mode.val.2)
    (annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode)

/-- The exact recovered physical flux has a genuine weak derivative; no
trace or derivative of the L2 source is an input. -/
theorem annularPhysicalQ_weak (bounded : lower < 1)
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (mode : HighAnnularMode) :
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    CollarWeakDerivative lower
      (annularPhysicalQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)
      (annularPhysicalQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode) :=
  collarWeakDerivative_scalar lower (annularInversePhase parameters mode.val.2)
    (annularInversePhaseSlope parameters mode.val.2) (annularInversePhase_hasDerivAt parameters mode.val.2)
    _ _ (annularNormalizedQ_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode)

theorem annularPhysicalP_eq_Q (field : annularEnergySpace lower length positive)
    (source : AnnularBulk lower) (mode : HighAnnularMode) :
    annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source mode =
      (-(annularDSymbol mode)⁻¹) • annularPhysicalQ parameters lower length positive lengthPositive widthHalf widthLength field source mode := by
  change annularDecodeMode parameters lower positive mode ((-(annularDSymbol mode)⁻¹) •
    annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source mode) = _
  exact map_smul _ _ _

def annularPhysicalPSlope (bounded : lower ≤ 1) (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) : CollarL2 (ComplexEuclidean 1) lower :=
  (-(annularDSymbol mode)⁻¹) •
    annularPhysicalQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded field source mode

theorem annularPhysicalP_weak (bounded : lower < 1)
    (source : AnnularForcing lower) (innerValue : AnnularBoundary) (mode : HighAnnularMode) :
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    CollarWeakDerivative lower
      (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)
      (annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode) := by
  dsimp only
  rw [annularPhysicalP_eq_Q]
  exact collarWeakDerivative_complex_smul lower _ _ _
    (annularPhysicalQ_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode)

end Flux
end Grad.AnnularReconstruction
