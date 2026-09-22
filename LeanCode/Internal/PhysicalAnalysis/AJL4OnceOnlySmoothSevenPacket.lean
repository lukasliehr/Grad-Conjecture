import AJL3SameOriginalSmoothRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularStrongOrbit
open Grad.AnnularCurrentSource Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularLowEnergy

private theorem scalarCoordinate_smooth {lower : ℝ} (curve : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ curve (Icc lower 1)) :
    ContDiffOn ℝ ∞ (fun radius => curve radius 0) (Icc lower 1) :=
  ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).contDiff.comp_contDiffOn smooth

def smoothKnownSevenPacket (lower : ℝ) (known : HighKnownSourceBulk lower)
    (f0 : FiniteSmoothStoredRow lower (known 0))
    (rf0 : FiniteSmoothStoredRow lower (known 1))
    (f2 : FiniteSmoothStoredRow lower (known 2)) :
    FiniteSmoothStoredRow lower (knownLowSevenPacket lower known) where
  support := f0.support ∪ rf0.support ∪ f2.support
  coefficient mode radius :=
    (f0.coefficient mode radius 0) • operatorBasis 4 +
    (rf0.coefficient mode radius 0) • operatorBasis 5 +
    (f2.coefficient mode radius 0) • operatorBasis 6
  smooth mode := (((scalarCoordinate_smooth _ (f0.smooth mode)).smul contDiffOn_const).add
    ((scalarCoordinate_smooth _ (rf0.smooth mode)).smul contDiffOn_const)).add
    ((scalarCoordinate_smooth _ (f2.smooth mode)).smul contDiffOn_const)
  outside mode outside radius := by
    have first : mode ∉ f0.support := fun inside => outside (Finset.mem_union_left _ (Finset.mem_union_left _ inside))
    have second : mode ∉ rf0.support := fun inside => outside (Finset.mem_union_left _ (Finset.mem_union_right _ inside))
    have third : mode ∉ f2.support := fun inside => outside (Finset.mem_union_right _ inside)
    rw [f0.outside mode first radius,rf0.outside mode second radius,f2.outside mode third radius]
    simp
  actual := by
    filter_upwards [knownLowSevenPacket_ae lower known,f0.actual,rf0.actual,f2.actual]
      with radius packet first second third
    intro mode
    rw [packet mode,first mode,second mode,third mode]

/-- The radius factor in the original third forcing is retained literally. -/
def FiniteSmoothStoredRow.radius {lower : ℝ} {row : DivisionRow 1 lower}
    (source : FiniteSmoothStoredRow lower row) (positive : 0 < lower) :
    FiniteSmoothStoredRow lower (radialRadiusRow lower positive row) where
  support := source.support
  coefficient mode radius := radius • source.coefficient mode radius
  smooth mode := contDiffOn_id.smul (source.smooth mode)
  outside mode outside radius := by rw [source.outside mode outside radius,smul_zero]
  actual := by
    filter_upwards [radialRadiusRow_ae lower positive row,source.actual] with radius weighted actual
    intro mode
    rw [weighted mode,actual mode]

/-- Physical decoding commutes with the original real radius multiplier. -/
theorem FiniteSmoothStoredRow.radius_physicalPolynomial_actual {lower : ℝ} {row : DivisionRow 1 lower}
    (source : FiniteSmoothStoredRow lower row) (parameters : PhaseParameters)
    (positive : 0 < lower) (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      (source.radius positive).physicalPolynomial parameters power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          (radius • Grad.AnnularCurrentLow.lowRhoPhysicalCoefficient parameters lower positive row radius mode) := by
  filter_upwards [(source.radius positive).physicalPolynomial_actual parameters positive power,
    radialRadiusRow_ae lower positive row] with radius actual weighted
  intro mode
  rw [actual mode]
  unfold Grad.AnnularCurrentLow.lowRhoPhysicalCoefficient
  rw [weighted mode]
  exact congrArg (fun value : ComplexEuclidean 1 =>
    (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) • value)
    (smul_comm _ radius (row mode radius))

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (core : OriginalSmoothSourceCore parameters)

/-- Only the three copied known source slots are inserted. -/
def smoothStrongSevenRow : FiniteSmoothStoredRow lower
    (knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded
      ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core))) :=
  smoothKnownSevenPacket lower _
    (smoothStrongKnownRow parameters lower positive bounded core length lengthPositive 0)
    (smoothStrongKnownRow parameters lower positive bounded core length lengthPositive 1)
    (smoothStrongKnownRow parameters lower positive bounded core length lengthPositive 2)

end Grad.AnnularSmoothSources
