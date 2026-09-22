import AJO4LiteralFullLowRowCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowClassical
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularRegularity
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.PhaseAlgebra

theorem lowRhoPhysicalCoefficient_real {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (radius : ℝ) (mode : ℤ × ℤ) :
    lowRhoPhysicalCoefficient parameters lower positive field radius mode =
      (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ • field mode radius := by
  unfold lowRhoPhysicalCoefficient
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact congrArg (fun scalar : ℂ => scalar • field mode radius)
    (Complex.ofReal_inv (lowRhoPhysicalWeight parameters lower positive radius mode)).symm

theorem lowRhoPhysicalCoefficient_encode {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (radius : ℝ) (mode : ℤ × ℤ) :
    field mode radius = lowRhoPhysicalWeight parameters lower positive radius mode •
      lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  rw [lowRhoPhysicalCoefficient_real, smul_smul,
    mul_inv_cancel₀ (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne', one_smul]

theorem lowRhoPhysicalCoefficient_storage {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower)
    (radius : ℝ) (mode : ℤ × ℤ) :
    lowStorageInverse lower positive radius • field mode radius =
      Real.exp (radialPhase parameters radius mode.2) •
        lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  rw [lowRhoPhysicalCoefficient_encode parameters lower positive field radius mode]
  rw [smul_smul]
  congr 1
  change lowStorageInverse lower positive radius *
    (lowStorageWeight lower positive radius * Real.exp (radialPhase parameters radius mode.2)) = _
  rw [← mul_assoc, mul_comm (lowStorageInverse lower positive radius), lowStorage_inverse, one_mul]

private theorem cancelMu (mu scalar : ℝ) (nonzero : mu ≠ 0) : mu * (scalar / mu) = scalar := by
  field_simp

/-- Algebra of the original xi balance after cancellation of rho storage. -/
theorem lowXiBalance {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mu p q a e : ℝ) (nonzero : mu ≠ 0) (value first : E) :
    mu • (((p + q) / mu) • ((e * (a * mu)) • value) + a • (e • first)) =
      (e * (a * mu)) • first + (e * (a * mu) * (p + q)) • value := by
  simp only [smul_add, smul_smul]
  have diagonal : mu * ((p + q) / mu * (e * (a * mu))) = e * (a * mu) * (p + q) := by
    rw [← mul_assoc, cancelMu mu (p + q) nonzero]
    ring
  rw [diagonal]
  have forcing : mu * (a * e) = e * (a * mu) := by ring
  rw [forcing, add_comm]

/-- Algebra of the original x balance, with its literal negative 1/r term. -/
theorem lowXBalance {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mu p inverseRadius n m e : ℝ) (nonzero : mu ≠ 0) (value cell angular : E) :
    mu • (((p - inverseRadius) / mu) • (e • value) +
      (n / mu) • (e • cell) + (m / mu) • (e • angular)) =
      e • ((-inverseRadius) • value + n • cell + m • angular) + (e * p) • value := by
  simp only [smul_add, smul_smul]
  have diagonal : mu * ((p - inverseRadius) / mu * e) = e * (-inverseRadius) + e * p := by
    rw [← mul_assoc, cancelMu mu (p - inverseRadius) nonzero]
    ring
  have cellLaw : mu * (n / mu * e) = e * n := by
    rw [← mul_assoc, cancelMu mu n nonzero, mul_comm]
  have angularLaw : mu * (m / mu * e) = e * m := by
    rw [← mul_assoc, cancelMu mu m nonzero, mul_comm]
  rw [diagonal, cellLaw, angularLaw, add_smul]
  abel

end Grad.AnnularLowClassical
