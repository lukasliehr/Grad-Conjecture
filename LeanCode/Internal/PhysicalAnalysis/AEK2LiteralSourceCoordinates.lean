import AEK1ActualInhomogeneousPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
  Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularCurrentEnergy

/-- Every Fourier/radial coefficient of the inhomogeneous packet is exactly
the independent `(F0, RF0, F2, f)` tuple. -/
theorem highKnownEightPacket_ae (lower : ℝ)
    (source : HighKnownSourceBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      highKnownEightPacket lower source mode radius =
        (source 0 mode radius 0) • operatorBasis 4 +
        (source 1 mode radius 0) • operatorBasis 5 +
        (source 2 mode radius 0) • operatorBasis 6 +
        (source 3 mode radius 0) • operatorBasis 7 := by
  rw [ae_all_iff]
  intro mode
  let first : DivisionRow 8 lower := bulkMatrixUnit lower 4 0 (source 0)
  let second : DivisionRow 8 lower := bulkMatrixUnit lower 5 0 (source 1)
  let third : DivisionRow 8 lower := bulkMatrixUnit lower 6 0 (source 2)
  let fourth : DivisionRow 8 lower := bulkMatrixUnit lower 7 0 (source 3)
  have exactSum : highKnownEightPacket lower source = first + second + third + fourth := rfl
  rw [exactSum]
  filter_upwards [bulkMatrixUnit_ae lower (4 : Fin 8) (0 : Fin 1) (source 0),
    bulkMatrixUnit_ae lower (5 : Fin 8) (0 : Fin 1) (source 1),
    bulkMatrixUnit_ae lower (6 : Fin 8) (0 : Fin 1) (source 2),
    bulkMatrixUnit_ae lower (7 : Fin 8) (0 : Fin 1) (source 3),
    Lp.coeFn_add (first mode) (second mode),
    Lp.coeFn_add (first mode + second mode) (third mode),
    Lp.coeFn_add (first mode + second mode + third mode) (fourth mode)]
      with radius one two three four sum12 sum123 sum1234
  change ((first mode + second mode) + third mode + fourth mode) radius = _
  have h12 : (first mode + second mode) radius =
      first mode radius + second mode radius := sum12
  have h123 : (first mode + second mode + third mode) radius =
      (first mode + second mode) radius + third mode radius := sum123
  have h1234 : (first mode + second mode + third mode + fourth mode) radius =
      (first mode + second mode + third mode) radius + fourth mode radius := sum1234
  exact h1234.trans (congrArg₂ (fun a b : ComplexEuclidean 8 => a + b)
    (h123.trans (congrArg₂ (fun a b : ComplexEuclidean 8 => a + b)
      (h12.trans (congrArg₂ (fun a b : ComplexEuclidean 8 => a + b)
        (one mode) (two mode))) (three mode))) (four mode))

/-- The inhomogeneous packet does not alter any unknown coordinate. -/
theorem highKnownEightPacket_unknowns_zero (lower : ℝ)
    (source : HighKnownSourceBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      ∀ coordinate : Fin 8, coordinate.val < 4 →
        highKnownEightPacket lower source mode radius coordinate = 0 := by
  filter_upwards [highKnownEightPacket_ae lower source] with radius actual
  intro mode coordinate unknown
  rw [actual mode]
  fin_cases coordinate <;> simp_all [operatorBasis]

/-- Adding known data to the accepted homogeneous energy packet changes
exactly slots four through seven. -/
def fullHighEightPacket (parameters : Grad.CartesianState.PhaseParameters)
    (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    (Grad.AnnularVariational.annularEnergySpace lower length positive ×
      HighKnownSourceBulk lower) →L[ℂ] DivisionRow 8 lower :=
  (Grad.AnnularCurrentEnergy.highEightEnergyPacket parameters lower length positive
    lengthPositive widthHalf widthLength).comp (ContinuousLinearMap.fst ℂ _ _) +
  (highKnownEightPacket lower).comp (ContinuousLinearMap.snd ℂ _ _)

end Grad.AnnularCurrentSource
