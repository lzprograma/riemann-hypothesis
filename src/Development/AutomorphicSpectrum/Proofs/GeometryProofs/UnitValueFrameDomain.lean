module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.UnitValue

theorem mem_regAt_of_pow_mul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {f u : Ω} (hf : f ≠ 0) (hf' : f⁻¹ ∈ regAt ξ p) {n : ℕ} (h : f ^ n * u ∈ regAt ξ p) : u ∈ regAt ξ p := by
  have hu : u = f⁻¹ ^ n * (f ^ n * u) := by
    rw [← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hf, _root_.one_pow, _root_.one_mul]
  rw [hu]
  exact mul_mem (pow_mem hf' n) h

theorem valAt_ne_zero_of_isUnitOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  intro X Ω _ ξ K _ J _ y z w cc f u hT hz hC hF hU
  have hequiv := _root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords X Ω ξ K J y hT z w hz hC
  have hch := GlobalTheory.CompanionTheory.Ar.ChgUnit.inChart_of_coordsAt hC cc (fun k => (hF.1 k).isUnit)
    ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ rfl
  have hreg : ∀ a, a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) cc →
      a ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ :=
    fun a ha => (hT.ring cc hch.1 a).1 ha _ hch
  obtain ⟨v, hv, hv0⟩ := hF.2
  have hfval : ValAt ξ z f v := (hequiv f v).2 hv
  have hf0 : f ≠ 0 := fun h0 =>
    hv0 (TieValue.val_unique hT.gen.inj (h0 ▸ hfval) ⟨hz, 0, map_zero _, map_zero _⟩)
  have hfi : f⁻¹ ∈ regAt ξ ⟨centre z, hz⟩ :=
    ChgUnit.mem_regAt_of_valAt (TieValue.val_inv hfval hv0) _ rfl
  obtain ⟨hu0, ⟨n, hn⟩, ⟨m, hm⟩⟩ := hU
  have hu := mem_regAt_of_pow_mul hf0 hfi (hreg _ hn)
  have hui := mem_regAt_of_pow_mul hf0 hfi (hreg _ hm)
  obtain ⟨r, hr0, hr⟩ := GlobalTheory.CompanionTheory.Ar.ChgUnit.exists_value_of_unit hT.gen z hz hu0 hu hui
  have hex : ∃ v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y u w v := ⟨r, (hequiv u r).1 hr⟩
  have hval : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = hex.choose := by
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dite_eq_left hex]
  have hc : GlobalTheory.CompanionTheory.Ar.ValAt ξ z u hex.choose := (hequiv u _).2 hex.choose_spec
  have heq : hex.choose = r := TieValue.val_unique hT.gen.inj hc hr
  rw [hval, heq]
  exact ⟨hr0, hr⟩

end GlobalTheory.CompanionTheory.Ar.UnitValue
