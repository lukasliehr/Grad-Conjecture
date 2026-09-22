import AKDB3SameScalarPolynomialGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints.Gauges
open Grad.PhysicalFamily Grad.ActualSmoothPhysicalField Grad.GaugeCoefficients.Physical.RadialLedger

namespace StartupRadialRelated
variable {symbol : ℤ → Spatial → ℝ}

theorem weighted_unique {dimension : ℕ} {first second raw : StartupL2 dimension}
    (one : StartupRadialRelated symbol first raw) (two : StartupRadialRelated symbol second raw) : first=second := by
  apply Lp.ext
  filter_upwards [one,two] with point one two
  apply lp.ext
  funext cell
  exact (one cell).trans (two cell).symm

theorem smoothDiskMultiplier {dimension : ℕ} {weighted original : StartupL2 dimension}
    (same : StartupRadialRelated symbol weighted original) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) :
    StartupRadialRelated symbol (startupSmoothDiskMultiplier dimension scalar smooth weighted)
      (startupSmoothDiskMultiplier dimension scalar smooth original) := by
  filter_upwards [same,startupSmoothDiskMultiplier_same dimension scalar smooth weighted,
    startupSmoothDiskMultiplier_same dimension scalar smooth original] with point same weightedValue originalValue
  intro cell
  rw [weightedValue cell,originalValue cell,same cell]
  exact smul_comm _ _ _

theorem tangentialPolynomial {weighted original : StartupL2 2} (same : StartupRadialRelated symbol weighted original) :
    StartupRadialRelated symbol (startupTangentialPolynomialKernel weighted) (startupTangentialPolynomialKernel original) :=
  ((same.value (startupComponentEntry 0 0)).smoothDiskMultiplier _ _).add
    ((same.value (startupComponentEntry 0 1)).smoothDiskMultiplier _ _)

end StartupRadialRelated

/-- The original weak force fixes the literal scalar for the SAME raw rows.
Only its proven mean-free primitive is used. -/
theorem StartupNativeWeakRows.scalar_polynomial {scale : ℝ} {psi : StartupL2 1} {rows : StartupNativeERRows}
    (weak : StartupNativeWeakRows scale psi rows) :
    psi = startupTangentialPolynomialKernel rows.gradient.field := by
  have force := (startupSame_projected_scalarPrimitive_force psi
    (originalValueKernel planarPartMap rows.covariant.field)
    (rows.knownForce.field-rows.forceCorrection.field) weak.force weak.mean).1
  rw [← startupFullCircle_planar rows.covariant.field] at force
  exact startupSame_scalarForce_polynomial_eq psi rows.vector.field
    (rows.knownForce.field-rows.forceCorrection.field) force weak.mean

/-- Transfer through the ORIGINAL radial phase, at unchanged width. No
spatial derivative is commuted through that phase; polynomial covariance
and the existing exact angular-kernel covariance suffice. -/
theorem StartupNativeWeakRows.weighted_scalar_polynomial {scale : ℝ} {psi weightedPsi : StartupL2 1}
    {weighted original : StartupNativeERRows} (weak : StartupNativeWeakRows scale psi original)
    {symbol : ℤ → Spatial → ℝ} (same : StartupNativeERRowsRelated symbol weighted original)
    (radial : ∀ cell (first second : Spatial), ‖first‖=‖second‖ → symbol cell first=symbol cell second)
    (scalarSame : StartupRadialRelated symbol weightedPsi psi) :
    weightedPsi = startupTangentialPolynomialKernel weighted.gradient.field := by
  have polynomialSame := (same.gradient radial).tangentialPolynomial
  rw [← weak.scalar_polynomial] at polynomialSame
  exact scalarSame.weighted_unique polynomialSame

theorem StartupNativeWeakRows.weighted_scalar_graph {scale : ℝ} {psi weightedPsi : StartupL2 1}
    {weighted original : StartupNativeERRows} (weak : StartupNativeWeakRows scale psi original)
    {symbol : ℤ → Spatial → ℝ} (same : StartupNativeERRowsRelated symbol weighted original)
    (radial : ∀ cell (first second : Spatial), ‖first‖=‖second‖ → symbol cell first=symbol cell second)
    (scalarSame : StartupRadialRelated symbol weightedPsi psi)
    (order weight : ℕ) (gradient : GraphGrade 2 order weight openUnitDisk)
    (gradientSame : base 2 order openUnitDisk (fun _ => weight) gradient = weighted.gradient.field) :
    ∃ scalar : GraphGrade 1 order weight openUnitDisk,
      base 1 order openUnitDisk (fun _ => weight) scalar = weightedPsi := by
  obtain ⟨scalar,actual⟩ := startupTangentialPolynomial_preservesGraph order weight gradient
  refine ⟨scalar,?_⟩
  rw [gradientSame,← weak.weighted_scalar_polynomial same radial scalarSame] at actual
  exact actual

end Grad.CartesianStartup
