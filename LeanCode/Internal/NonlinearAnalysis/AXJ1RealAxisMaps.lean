import AXL26LiftConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open scoped ComplexConjugate

namespace Grad.ChartAxisProjections

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges Grad.CompletedReality Grad.PhysicalCoordinates

variable {parameters : PhaseParameters}

def realAxisDataSubmodule (parameters : PhaseParameters) : Submodule ℝ (AxisData parameters) where
  carrier := RealAxisData
  zero_mem' := by
    constructor <;> intro cell index <;> simp
  add_mem' := by
    intro first second realFirst realSecond
    constructor
    · intro cell index
      change first.1.val (-cell) index + second.1.val (-cell) index =
        conj (first.1.val cell index + second.1.val cell index)
      rw [realFirst.1, realSecond.1, map_add]
    · intro cell index
      change first.2.val (-cell) index + second.2.val (-cell) index =
        conj (first.2.val cell index + second.2.val cell index)
      rw [realFirst.2, realSecond.2, map_add]
  smul_mem' := by
    intro scalar data real
    constructor
    · intro cell index
      change (scalar : ℂ) * data.1.val (-cell) index = conj ((scalar : ℂ) * data.1.val cell index)
      rw [real.1, map_mul, Complex.conj_ofReal]
    · intro cell index
      change (scalar : ℂ) * data.2.val (-cell) index = conj ((scalar : ℂ) * data.2.val cell index)
      rw [real.2, map_mul, Complex.conj_ofReal]

abbrev RealAxis (parameters : PhaseParameters) := realAxisDataSubmodule parameters

theorem axisData_ext {first second : AxisData parameters}
    (coefficients : (first.1.val, first.2.val) = (second.1.val, second.2.val)) : first = second :=
  Prod.ext (Subtype.ext (congrArg Prod.fst coefficients)) (Subtype.ext (congrArg Prod.snd coefficients))

def chartKappaLinear (parameters : PhaseParameters) :
    Grad.SmoothingFamily.StateCore parameters →ₗ[ℂ] AxisData parameters where
  toFun := chartKappaData parameters
  map_add' first second := by
    apply Prod.ext
    · apply Subtype.ext
      funext cell
      have subtract := scalarOriginGradient_sub (first.2.2 + second.2.2) second.2.2 cell
      rw [add_sub_cancel_right] at subtract
      exact eq_add_of_sub_eq subtract.symm
    · exact map_add ((tangentToAxis parameters).comp (smoothingToTangent parameters)) first.1 second.1
  map_smul' scalar direction := by
    apply Prod.ext
    · apply Subtype.ext
      funext cell
      exact scalarOriginGradient_smul scalar direction.2.2 cell
    · exact map_smul ((tangentToAxis parameters).comp (smoothingToTangent parameters)) scalar direction.1

theorem chartKappa_real (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (direction : stateSmoothRange parameters reference insideR) :
    RealAxisData (chartKappaData parameters direction.val) := by
  obtain ⟨axisReal, _, scalarReal⟩ := stateChart_real parameters reference insideR direction
  constructor
  · intro cell index
    have equality := scalarOriginGradient_conjugate direction.val.2.2 (-cell)
    rw [scalarReal, neg_neg] at equality
    exact congrArg (fun vector : ComplexEuclidean 2 => vector index) equality
  · exact axisReal

def realChartKappa (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    stateSmoothRange parameters reference insideR →ₗ[ℝ] RealAxis parameters where
  toFun direction := ⟨chartKappaData parameters direction.val, chartKappa_real reference insideR direction⟩
  map_add' first second := Subtype.ext ((chartKappaLinear parameters).map_add first.val second.val)
  map_smul' scalar direction := Subtype.ext (((chartKappaLinear parameters).restrictScalars ℝ).map_smul scalar direction.val)

theorem extractionData_real (cellLength : ℝ) (source : sourceSmoothRange parameters) :
    RealAxisData (extractionData cellLength source.val) := by
  have realSource := ((mem_sourceSmoothRange parameters source.val).1 source.property).2
  constructor
  · intro cell index
    have equality := sigmaExtraction_conjugate source.val (-cell)
    rw [realSource, neg_neg] at equality
    exact congrArg (fun vector : ComplexEuclidean 2 => vector index) equality
  · intro cell index
    have equality := etaExtraction_conjugate cellLength source.val (-cell)
    rw [realSource, neg_neg] at equality
    exact congrArg (fun vector : ComplexEuclidean 2 => vector index) equality

def realExtraction (parameters : PhaseParameters) (cellLength : ℝ) :
    sourceSmoothRange parameters →ₗ[ℝ] RealAxis parameters where
  toFun source := ⟨extractionData cellLength source.val, extractionData_real cellLength source⟩
  map_add' first second := Subtype.ext ((extractionLinear parameters cellLength).map_add first.val second.val)
  map_smul' scalar source := Subtype.ext (((extractionLinear parameters cellLength).restrictScalars ℝ).map_smul scalar source.val)

end Grad.ChartAxisProjections
