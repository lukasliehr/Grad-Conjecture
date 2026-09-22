import SCD30DivisionStatement

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

/-- Immediate source-collar consumer: the extra angular derivative needed
in RG3 is paid at exactly source grade t+4. This constructs the unique
actual divided field, not an inverse of radius multiplication on arbitrary L2. -/
theorem angularSourceDivisionConsumer (tangential : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (dimension : ℕ) (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower),
        lower ≤ 1 / 2 →
        ∀ field : AGrade parameters dimension (tangential + 4),
          OriginalValueFlat parameters (by omega) field →
          ∃ result : annularDerivativeGraph dimension lower positive 0,
            ‖result‖ ≤ constant * ‖field‖ ∧
            RepresentsFlatQuotient lower positive parameters (tangential + 1) 0 field result ∧
            ∀ other : annularDerivativeGraph dimension lower positive 0,
              RepresentsFlatQuotient lower positive parameters (tangential + 1) 0 field other → other = result :=
  actualFlatSourceDivision (tangential + 1) 0

/-- Positive radial regularity remains part of the same literal graph,
with no endpoint condition or first-axis-jet condition added to the source. -/
theorem radialSourceDivisionConsumer (tangential : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (dimension : ℕ) (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower),
        lower ≤ 1 / 2 →
        ∀ field : AGrade parameters dimension (tangential + 5),
          OriginalValueFlat parameters (by omega) field →
          ∃ result : annularDerivativeGraph dimension lower positive 1,
            ‖result‖ ≤ constant * ‖field‖ ∧
            RepresentsFlatQuotient lower positive parameters (tangential + 1) 1 field result ∧
            ∀ other : annularDerivativeGraph dimension lower positive 1,
              RepresentsFlatQuotient lower positive parameters (tangential + 1) 1 field other → other = result :=
  actualFlatSourceDivision (tangential + 1) 1

end Grad.SourceCollarDivision
