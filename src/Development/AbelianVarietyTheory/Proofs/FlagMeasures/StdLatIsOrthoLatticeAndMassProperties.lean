module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.StdMass


open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ} (hL : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    h.IsSymm := by
  unfold _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice at hL
  obtain ⟨e, -, hspan, -, horth⟩ := hL
  refine LinearMap.IsSymm.mk fun x y => ?_
  obtain ⟨c, rfl⟩ := _root_.Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.exists_coord hspan x
  obtain ⟨d, rfl⟩ := _root_.Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.exists_coord hspan y
  rw [_root_.Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.form_sum horth, _root_.Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.form_sum horth]

  simp only [map_sum, starRingEnd_apply, star_mul, star_star]

open NumberField Matrix in
open scoped ENNReal Classical in
private theorem massU_zero_eq_one (K : Type) [Field K] [NumberField K] [StarRing K] :
    _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 := by
  have hsub : ∀ M N : Submodule (𝓞 K) (Fin 0 → K), M = N := fun M N => Subsingleton.elim M N
  haveI : Subsingleton ((Fin 0 → K) ≃ₗ[K] (Fin 0 → K)) :=
    ⟨fun f g => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
  have hlat : Submodule.IsLattice K (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := _root_.Formalism.HermitianLattices.Ext.L3.isLattice_of_ortho (_root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K 0)
  have hfull : Submodule.IsFullLattice K (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) :=
    { toIsLattice := hlat, span_eq_top := Subsingleton.elim _ _ }
  have hgen : _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 ∈ _root_.Formalism.HermitianLatticesTheory.genus (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) := by
    unfold _root_.Formalism.HermitianLatticesTheory.genus _root_.Formalism.HermitianLatticesTheory.SameGenus
    exact ⟨hfull, fun p _ => ⟨1, one_mem _, hsub _ _⟩⟩
  have hs : ∃ s, _root_.Formalism.ThetaLiftIndependence.IsClassReps (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0) s := by
    refine ⟨{_root_.Formalism.MainNotions.S.Cnt.stdLat K 0}, ?_⟩
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps
    refine ⟨fun M hM => ?_, fun M _ => ⟨_root_.Formalism.MainNotions.S.Cnt.stdLat K 0,
      ⟨Finset.mem_singleton_self _, 1, one_mem _, hsub _ _⟩,
      fun N hN => Finset.mem_singleton.mp hN.1⟩⟩
    rw [Finset.mem_singleton.mp hM]
    exact hgen
  have hchoose : hs.choose = {_root_.Formalism.MainNotions.S.Cnt.stdLat K 0} := by
    have hspec := hs.choose_spec
    unfold _root_.Formalism.ThetaLiftIndependence.IsClassReps at hspec
    obtain ⟨N, ⟨hN, -⟩, -⟩ := hspec.2 _ hgen
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨?_, fun M _ => hsub _ _⟩
    have hN' : N = _root_.Formalism.MainNotions.S.Cnt.stdLat K 0 := hsub _ _
    exact hN' ▸ hN
  have hcard : Nat.card (_root_.Formalism.ThetaLiftIndependence.autL (_root_.Formalism.MainNotions.S.Cnt.stdH K 0) (_root_.Formalism.MainNotions.S.Cnt.stdLat K 0)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨inferInstance, ⟨⟨1, ?_⟩⟩⟩
    unfold _root_.Formalism.ThetaLiftIndependence.autL
    exact ⟨one_mem _, hsub _ _⟩
  unfold _root_.Formalism.MainNotions.S.Cnt.massU
  rw [_root_.Formalism.HermitianLatticesTheory.massBasic_mass_eq _ _ hs, hchoose, Finset.sum_singleton, hcard]
  norm_num


open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.StdMass.main : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K], _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ j : ℕ, (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm ∧
      _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j ∧ 0 < _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.Formalism.MainNotions.S.Cnt.massU K 0 = 1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h L j →
        _root_.Formalism.HermitianLatticesTheory.mass h L = _root_.Formalism.MainNotions.S.Cnt.massU K j ∧ _root_.GlobalTheory.Mass.PD h := by
  intro K _ _ _ hK j
  have hsymm : (_root_.Formalism.MainNotions.S.Cnt.stdH K j).IsSymm := _root_.Formalism.HermitianLattices.Ext.L3.stdForm_isSymm K j
  have hortho : _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice (_root_.Formalism.MainNotions.S.Cnt.stdH K j) (_root_.Formalism.MainNotions.S.Cnt.stdLat K j) j := _root_.Formalism.MainNotions.StandardLattice.stdLat_ortho K j
  refine ⟨hsymm, hortho, ?_, massU_zero_eq_one K, fun V _ _ _ _ h L hL => ⟨?_, ?_⟩⟩
  · unfold _root_.Formalism.MainNotions.S.Cnt.massU
    exact _root_.ReciprocityTheory.ChartRestriction.L3.mass_pos_of_ortho hK hsymm hortho
  · exact (_root_.Formalism.MainNotions.StandardLattice.mass_ortho K hK j V h L hL).trans rfl
  · have hpos := _root_.Formalism.HermitianLattices.Ext.L3.isTotPosDef_of_ortho hK (_root_.GlobalTheory.Mass.StdMass.isSymm_of_ortho hL) hL
    unfold _root_.Formalism.HermitianLattices.Ext.L3.IsTotPosDef at hpos
    unfold _root_.GlobalTheory.Mass.PD
    exact fun τ x hx => hpos x hx τ

end GlobalTheory.Mass.StdMass
