module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveAppTopOfSmoothOfIsProperOfGeometrically
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ConnSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  apply _root_.GlobalTheory.AlgGroup.preconnectedSpace_of_functions <;> assumption

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem exists_geometricallyConnected_away_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ GeometricallyConnected (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s K _ x hp hs hc
  have hp' : IsProjBy s := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := isProper_of_isProjBy R Z s hp'
  have h₀ : IsPullback (pullback.fst s (spMap x)) (pullback.snd s (spMap x)) s
      (Spec.map (CommRingCat.ofHom x)) := IsPullback.of_hasPullback _ _
  have hbij := bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K _
    (pullback.snd s (spMap x)) inferInstance inferInstance hc
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (GlobalTheory.AlgGroup.triv_pull _)
  obtain ⟨x₀, -⟩ := (pullback.snd s (spMap x)).surjective (⊥ : PrimeSpectrum K)
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul K (0 : Fin P.a → K), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector x P.D₀ v hv0 (hline hbij.2)
  let p : PrimeSpectrum R := s ((pullback.fst s (spMap x)) x₀)
  have hpx : ∀ a : R, a ∉ p.asIdeal → x a ≠ 0 := fun a ha h0 => by
    have e : p = Spec.map (CommRingCat.ofHom x) (pullback.snd s (spMap x) x₀) :=
      congrArg (fun t => t x₀) h₀.w
    apply ha
    rw [e]
    change x a ∈ (pullback.snd s (spMap x) x₀).asIdeal
    rw [h0]
    exact zero_mem _
  obtain ⟨_, ⟨ε, rfl⟩, hε, hεs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (Set.range s : Set (PrimeSpectrum R)) from ⟨_, rfl⟩) s.isOpenMap.isOpen_range
  refine ⟨δ * ε, by rw [map_mul]; exact mul_ne_zero hδ (hpx ε hε), ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap (Localization.Away (δ * ε)) F).comp (algebraMap R _)
  have hg : IsUnit (g δ * g ε) := by
    rw [← map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (δ * ε)) (δ * ε)).map
      (algebraMap (Localization.Away (δ * ε)) F)
  have h' : IsPullback (fst ≫ pullback.fst s (spMap (algebraMap R (Localization.Away (δ * ε))))) snd s
      (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s _)
    rwa [← Spec.map_comp] at this
  have hmem : Spec.map (CommRingCat.ofHom g) (⊥ : PrimeSpectrum F) ∈ Set.range s :=
    hεs fun h0 : g ε ∈ (⊥ : Ideal F) => (isUnit_of_mul_isUnit_right hg).ne_zero h0
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨y, -⟩ := Scheme.exists_preimage_of_isPullback h' z _ hz
  have := GlobalTheory.AlgGroup.preconnectedSpace_of_line P h' _ (hker F _ (isUnit_of_mul_isUnit_left hg))
  exact ⟨⟨y⟩⟩

end GlobalTheory.ConnSpread
