import AJL1FiniteSmoothPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularStrongOrbit
open Grad.AnnularCurrentSource Grad.GaugeCoefficients.Physical.WeightedTrace

variable {dimension : ℕ} {lower : ℝ} {field target : DivisionRow dimension lower}

def FiniteSmoothStoredRow.scalar (source : FiniteSmoothStoredRow lower field)
    (scalar : (ℤ × ℤ) → ℂ) (same : ∀ mode, target mode = scalar mode • field mode) :
    FiniteSmoothStoredRow lower target where
  support := source.support
  coefficient mode radius := scalar mode • source.coefficient mode radius
  smooth mode := (source.smooth mode).const_smul _
  outside mode outside radius := by rw [source.outside mode outside radius,smul_zero]
  actual := by
    rw [ae_all_iff]
    intro mode
    filter_upwards [source.actual,Lp.coeFn_smul (scalar mode) (field mode)] with radius actual scalarLaw
    rw [same mode,scalarLaw]
    exact congrArg (fun value : ComplexEuclidean dimension => scalar mode • value) (actual mode)

/-- Ordinary stored f and strengthened g supplied by the original smooth core. -/
def finiteOrdinarySmoothRow (dimension : ℕ) (lower : ℝ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    FiniteSmoothStoredRow lower (finiteSmoothRadialSource dimension lower core) where
  support := core.support
  coefficient mode := (core mode).val.val.1
  smooth mode := (show ContDiff ℝ ∞ (core mode).val.val.1 from (core mode).property).contDiffOn
  outside mode outside radius := by
    rw [Finsupp.notMem_support_iff.mp outside]
    rfl
  actual := by
    rw [ae_all_iff]
    intro mode
    exact (finiteSmoothRadialSource_radial dimension lower core mode).2

/-- Exact r dr graph storage, including its original square root. -/
def finiteGraphSmoothRow (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    FiniteSmoothStoredRow lower
      (annularSourceCoordinate parameters dimension lower 0 0 0 (finiteSourceCore parameters dimension lower 0 0 core)) where
  support := core.support
  coefficient mode radius := Real.sqrt radius • (core mode).val.val.1 radius
  smooth mode := (contDiffOn_id.sqrt (fun radius inside => (positive.trans_le inside.1).ne')).smul
    (show ContDiff ℝ ∞ (core mode).val.val.1 from (core mode).property).contDiffOn
  outside mode outside radius := by
    rw [Finsupp.notMem_support_iff.mp outside]
    exact smul_zero _
  actual := by
    rw [ae_all_iff]
    intro mode
    change ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      weightedRadialCoordinate dimension lower 0
        (finiteSourceCore parameters dimension lower 0 0 core mode) radius = _
    rw [finiteSourceCore_apply,weightedRadialCoordinate_core_zero]
    exact radialToLp_ae lower (core mode).val.val.1 (core mode).val.val.1.continuous

variable {row : DivisionRow 1 lower}

def FiniteSmoothStoredRow.highWeight (source : FiniteSmoothStoredRow lower row)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    FiniteSmoothStoredRow lower (divisionHighWeight lower positive bounded row) where
  support := source.support
  coefficient mode radius := ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • source.coefficient mode radius
  smooth mode := (Complex.ofRealCLM.contDiff.comp_contDiffOn (positivePower_smooth lower positive (-9 / 4 : ℝ))).smul
    (source.smooth mode)
  outside mode outside radius := by rw [source.outside mode outside radius,smul_zero]
  actual := by
    filter_upwards [source.actual,divisionHighWeight_ae lower positive bounded row] with radius actual weighted
    intro mode
    rw [weighted mode,actual mode]

end Grad.AnnularSmoothSources
