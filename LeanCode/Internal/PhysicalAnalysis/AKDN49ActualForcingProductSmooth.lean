import AKDN48LinearEulerEnergyAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.QuotientProjection Grad.AnnularOriginalCoreRealization

def actualPhysicalPrimitiveCurve (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (source : SmoothQuotient parameters) (row : Fin 3) (injection : Fin 7) (slot : Fin 4)
    (power : ℕ) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) power 0 radius
    (hilbertSlotInjection parameters injection (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power radius))

theorem actualPhysicalPrimitiveCurve_smooth (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (source : SmoothQuotient parameters) (row : Fin 3) (injection : Fin 7) (slot : Fin 4) (power : ℕ) :
    ContDiffOn ℝ ∞ (actualPhysicalPrimitiveCurve parameters length compact lower positive bounded state source row injection slot power)
      (Icc lower 1) := by
  let primitive := actualCartesianPrimitiveCurve parameters length lower positive bounded source slot
  let injected := fun grade point => hilbertSlotInjection parameters injection (primitive grade point)
  have smooth (grade : ℕ) : ContDiffOn ℝ ∞ (injected grade) (Icc lower 1) :=
    ((hilbertSlotInjection parameters injection).restrictScalars ℝ).contDiff.comp_contDiffOn
      ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).smooth grade)
  have same (grade reserve : ℕ) (point : ℝ) (inside : point ∈ Icc lower 1) (mode : ℤ × ℤ) :
      injected (grade+reserve) point mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • injected grade point mode := by
    have primitiveSame : primitive (grade+reserve) point mode =
        (annularFrequency mode.1 mode.2 : ℂ)^reserve • primitive grade point mode :=
      (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).shift bounded grade reserve point inside mode
    change matrixUnit injection (0 : Fin 1) (primitive (grade+reserve) point mode)=_
    rw [primitiveSame,map_smul]
    rfl
  exact coherentConjugatedKernelCurve_smooth parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) injected smooth same power
    (originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive bounded row power)

def actualKappaPrimitiveCurve (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (source : SmoothQuotient parameters) (component : Fin 3) (slot : Fin 4)
    (power : ℕ) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive bounded.le
    (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component)
    power 0 radius (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power radius)

theorem actualKappaPrimitiveCurve_smooth (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (source : SmoothQuotient parameters) (component : Fin 3) (slot : Fin 4) (power : ℕ) :
    ContDiffOn ℝ ∞ (actualKappaPrimitiveCurve parameters length compact lower positive bounded state source component slot power)
      (Icc lower 1) :=
  coherentConjugatedKernelCurve_smooth parameters lower positive bounded.le
    (actualSourceKappaKernel parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low component)
    (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot)
    (actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).smooth
    ((actualCartesianPrimitiveRadialCurves parameters length lower positive bounded source slot).shift bounded) power
    (actualSourceKappaKernel_smooth parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded component power)

end Grad.OriginalCartesianTameEstimate
