import AJB16ActualLowSolutionGeneratorDomains

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal ContDiff
namespace Grad.AnnularOrbitGenerators
open Grad.CartesianState Grad.FourierGrade

/-- Genuine finite Fourier data have smooth orbits in the complete lp norm. -/
theorem finiteLpCharacterOrbit_contDiff {ι V : Type*} [DecidableEq ι]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (frequency : ι → ℤ) (field : lp (fun _ : ι => V) 2) (orbit : ℝ → lp (fun _ : ι => V) 2)
    (character : ∀ time index, orbit time index = cellExponential (frequency index) time • field index)
    (support : Finset ι) (finite : ∀ index, index ∉ support → field index = 0) :
    ContDiff ℝ ∞ orbit := by
  have formula (time : ℝ) : orbit time = ∑ index ∈ support,
      cellExponential (frequency index) time • (lp.single 2 index (field index) : lp (fun _ : ι => V) 2) := by
    apply lp.ext
    funext index
    rw [character, lp.coeFn_sum, Finset.sum_apply]
    symm
    change (∑ other ∈ support, cellExponential (frequency other) time •
      (lp.single 2 other (field other) : lp (fun _ : ι => V) 2) index) = _
    simp only [lp.single_apply, Pi.single_apply]
    rw [Finset.sum_eq_single index]
    · simp only [ite_true]
    · intro other _ different
      simp only [if_neg (Ne.symm different), smul_zero]
    · intro outside
      rw [finite index outside]
      simp only [ite_true, smul_zero]
  have same : orbit = fun time => ∑ index ∈ support,
      cellExponential (frequency index) time • (lp.single 2 index (field index) : lp (fun _ : ι => V) 2) := funext formula
  rw [same]
  apply ContDiff.sum
  intro index _
  have scalarSmooth : ContDiff ℝ ∞ (cellExponential (frequency index)) := by
    unfold cellExponential
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  exact scalarSmooth.smul contDiff_const

end Grad.AnnularOrbitGenerators
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit Grad.AnnularOrbitGenerators
open Grad.AnnularCoupledOrbit Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual independent low bulk and incoming coordinates, finite in the
same original mode set, have a smooth original data orbit. -/
theorem lowFiniteDataOrbit_contDiff (lower : ℝ) (data : LowEnergyData lower) (support : Finset LowAnnularIndex)
    (bulkFinite : ∀ index, index ∉ support → data.ofLp.1 index = 0)
    (incomingFinite : ∀ index, index ∉ support → data.ofLp.2 index = 0) :
    ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data) := by
  classical
  have bulkSmooth : ContDiff ℝ ∞ (fun time : ℝ => lowBulkTranslation lower (0, time) data.ofLp.1) :=
    finiteLpCharacterOrbit_contDiff (fun index : LowAnnularIndex => index.2.val.2) data.ofLp.1
      (fun time => lowBulkTranslation lower (0, time) data.ofLp.1)
      (fun time index => by rw [lowBulkTranslation_apply, orbitCharacter_cell]) support bulkFinite
  have incomingSmooth : ContDiff ℝ ∞ (fun time : ℝ => lowBoundaryTranslation (0, time) data.ofLp.2) :=
    finiteLpCharacterOrbit_contDiff (fun index : LowAnnularIndex => index.2.val.2) data.ofLp.2
      (fun time => lowBoundaryTranslation (0, time) data.ofLp.2)
      (fun time index => by rw [lowBoundaryTranslation_apply, orbitCharacter_cell]) support incomingFinite
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
    (bulkSmooth.prodMk incomingSmooth)

/-- Actual finite Fourier data give all generator powers of the SAME original
solution as genuine graph elements; no smooth-solution premise is assumed. -/
theorem lowFiniteDataInverse_generator (parameters : PhaseParameters) (length compact lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      lowCurrentNeighborhood parameters length compact)
    (data : LowEnergyData lower) (support : Finset LowAnnularIndex)
    (bulkFinite : ∀ index, index ∉ support → data.ofLp.1 index = 0)
    (incomingFinite : ∀ index, index ∉ support → data.ofLp.2 index = 0) (order : ℕ) :
    ∃ generator : lowEnergyGraph lower length positive, ∀ (coordinate : Fin 2) (index : LowAnnularIndex),
      generator.val coordinate index = (Complex.I * (index.2.val.2 : ℂ)) ^ order •
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state data).val coordinate index := by
  refine ⟨actualLowSolutionCellGenerator parameters length compact lower lengthPositive positive bounded state data order, ?_⟩
  intro coordinate index
  exact actualLowSolutionCellGenerator_coefficients parameters length compact lower lengthPositive positive bounded state small data
    (lowFiniteDataOrbit_contDiff lower data support bulkFinite incomingFinite) order coordinate index

end Grad.AnnularLowOrbit
