module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ConnFibre

open GlobalTheory.AbLaw.Seesaw

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  apply _root_.GlobalTheory.AlgGroup.preconnectedSpace_of_functions <;> assumption

theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom :=
  _root_.GlobalTheory.AlgGroup.surjective_appTop p

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' :=
  _root_.GlobalTheory.AlgGroup.preconnectedSpace_of_line P h v hv

theorem geometricallyConnected_of_closedFibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))), Smooth B.hom → IsProjBy B.hom → ∀ (Y₀ : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1))))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (thick V (IsLocalRing.maximalIdeal V) 0) → GeometricallyConnected Y₀.hom → GeometricallyConnected B.hom := by
  intro V _ _ _ B hs hp Y₀ b hb hc
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj V B.left B.hom hs hp _ (Inh.trivLB_isLB _)
  have hpr : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy V B.left B.hom hp
  let L := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* L := (algebraMap (IsLocalRing.ResidueField V) L).comp (IsLocalRing.residue V)
  have hg₀ : ∀ a, g₀ a = 0 ↔ a ∈ IsLocalRing.maximalIdeal V := fun a =>
    (map_eq_zero (algebraMap (IsLocalRing.ResidueField V) L)).trans (IsLocalRing.residue_eq_zero_iff a)
  let q : V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1) →+* L :=
    Ideal.Quotient.lift _ g₀ fun a ha => (hg₀ a).2 (by simpa using ha)
  let y₀ : Spec (CommRingCat.of L) ⟶ _ := Spec.map (CommRingCat.ofHom q)
  have h₀ : IsPullback (pullback.fst Y₀.hom y₀ ≫ b) (pullback.snd Y₀.hom y₀) B.hom
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback Y₀.hom y₀).paste_horiz hb
    rwa [← Spec.map_comp] at this
  have hs₀ : Smooth Y₀.hom := MorphismProperty.of_isPullback hb hs
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ Y₀.hom hs₀ hc
  have hint : IsIntegral (pullback Y₀.hom y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback Y₀.hom y₀)
  have hpr₀ : IsProper (pullback.snd Y₀.hom y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback Y₀.hom y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst Y₀.hom y₀ ≫ b) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  have hδ' : IsUnit δ := by
    by_contra hn
    exact hδ ((hg₀ δ).2 hn)
  have hsurj : Surjective B.hom := by
    let O : (Spec (CommRingCat.of V)).Opens := ⟨Set.range B.hom, B.hom.isOpenMap.isOpen_range⟩
    have hO : O = ⊤ := by
      refine (IsLocalRing.closedPoint_mem_iff O).1 ⟨(pullback.fst Y₀.hom y₀ ≫ b) x₀, ?_⟩
      have e : B.hom ((pullback.fst Y₀.hom y₀ ≫ b) x₀) =
          Spec.map (CommRingCat.ofHom g₀) (pullback.snd Y₀.hom y₀ x₀) := congrArg (fun t => t x₀) h₀.w
      refine e.trans (PrimeSpectrum.ext ?_)
      refine ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le (PrimeSpectrum.isPrime _).ne_top
        fun a ha => ?_).symm
      change g₀ a ∈ (pullback.snd Y₀.hom y₀ x₀).asIdeal
      rw [(hg₀ a).2 ha]
      exact zero_mem _
    exact ⟨fun z => hO.ge (Set.mem_univ z)⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Z fst snd h => ?_⟩
  have : Surjective snd := MorphismProperty.of_isPullback h hsurj
  obtain ⟨z, -⟩ := snd.surjective (⊥ : PrimeSpectrum F)
  have := preconnectedSpace_of_line P h _ (hker F _ (hδ'.map _))
  exact ⟨⟨z⟩⟩

end GlobalTheory.ConnFibre
