import AAZ7PhysicalJetDerivativeInduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularFirstRawSlope (lower : ℝ) (positive : 0 < lower) (length : ℝ)
    (initial : AnnularRawState lower) (source : AnnularRawSource lower) : AnnularRawState lower :=
  (annularRawRadiusPower lower positive 1 initial.1 +
    annularRawSymbol lower annularAngularISymbol (annularRawRadiusPower lower positive 2 initial.2) +
    annularRawSymbol lower (annularLongitudinalISymbol length) initial.2 + source.2.1 +
    annularRawSymbol lower (annularLongitudinalSourceSymbol length) source.2.2,
   (-2 : ℝ) • annularRawRadiusPower lower positive 1 initial.2 +
    annularRawSymbol lower (fun mode => -annularDSymbol mode) initial.1 + source.1)

theorem annularPhysicalStateJet_one (lower : ℝ) (positive : 0 < lower) (length : ℝ)
    (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower) :
    annularPhysicalStateJet lower positive length initial source 1 =
      annularFirstRawSlope lower positive length initial (source 0) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, annularPhysicalStateJet_succ]
  simp only [annularLeibniz_zero, annularPhysicalStateJet_zero]
  rfl

/-- The exact original second coefficient splits into its radial and
cell-frequency pieces; no cell frequency is divided out. -/
theorem annularSecondCurve_split (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (annularSecondRealCurve lower length positive mode) field =
      (mode.val.1 : ℝ) • annularRadiusPower lower positive 2 field +
        ((mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2) : ℝ) • field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (annularSecondRealCurve lower length positive mode) field,
    collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive) (annularRadiusInverse lower positive field),
    collarScalar_ae 1 lower (annularInverseRadiusCurve lower positive) field,
    Lp.coeFn_add ((mode.val.1 : ℝ) • annularRadiusPower lower positive 2 field)
      (((mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2) : ℝ) • field),
    Lp.coeFn_smul (mode.val.1 : ℝ) (annularRadiusPower lower positive 2 field),
    Lp.coeFn_smul ((mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2) : ℝ) field]
    with radius coefficient outer inner sumLaw first second
  rw [coefficient, sumLaw, Pi.add_apply, first, second, Pi.smul_apply, Pi.smul_apply]
  change _ = (mode.val.1 : ℝ) • annularRadiusInverse lower positive (annularRadiusInverse lower positive field) radius + _
  rw [outer, inner, smul_smul, smul_smul, ← add_smul]
  change ((mode.val.1 : ℝ) / (max lower radius) ^ 2 +
    (mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2)) • field radius =
    ((mode.val.1 : ℝ) * (1 / max lower radius) * (1 / max lower radius) +
      (mode.val.2 : ℝ) ^ 2 / ((mode.val.1 : ℝ) * length ^ 2)) • field radius
  congr 1
  ring

theorem annularSecondCurve_I_split (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode) field =
      annularAngularISymbol mode • annularRadiusPower lower positive 2 field +
        annularLongitudinalISymbol length mode • field := by
  rw [annularSecondCurve_split, smul_add]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  rfl

theorem annularFirstSlope_decode (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (length : ℝ) (initial : AnnularRawState lower) (source : AnnularRawSource lower) (mode : HighAnnularMode) :
    annularDecodeMode parameters lower positive mode ((annularFirstRawSlope lower positive length initial source).1 mode) =
      annularRadiusPower lower positive 1 (annularDecodeMode parameters lower positive mode (initial.1 mode)) +
        Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
          (annularDecodeMode parameters lower positive mode (initial.2 mode)) +
        annularDecodeMode parameters lower positive mode (source.2.1 mode) +
        annularLongitudinalSourceSymbol length mode • annularDecodeMode parameters lower positive mode (source.2.2 mode) := by
  change annularDecodeMode parameters lower positive mode
    (annularRadiusPower lower positive 1 (initial.1 mode) +
      annularAngularISymbol mode • annularRadiusPower lower positive 2 (initial.2 mode) +
      annularLongitudinalISymbol length mode • initial.2 mode + source.2.1 mode +
      annularLongitudinalSourceSymbol length mode • source.2.2 mode) = _
  rw [map_add, map_add, map_add, map_add,
    (annularDecodeMode parameters lower positive mode).map_smul,
    (annularDecodeMode parameters lower positive mode).map_smul,
    (annularDecodeMode parameters lower positive mode).map_smul,
    annularRadiusPower_decode, annularRadiusPower_decode, annularSecondCurve_I_split]
  abel

end Grad.AnnularRadialJets
