module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix

namespace GlobalTheory.LocalConjugacy
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

noncomputable def coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V) : Submodule (𝓞 E) (Fin V.rank → E) :=
  L.map (V.frame.equivFun.restrictScalars (𝓞 E)).toLinearMap

theorem span_eq_top_of_unimodular (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    Submodule.span E (L : Set V.V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hu V.herm h.fg

theorem isLattice_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Submodule.IsLattice E L)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by exact V.baseLattice_isUnimodular) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (coordLat V L) := by
  refine ⟨h.fg.map _, ?_⟩
  have : (coordLat V L : Set (Fin V.rank → E)) = V.frame.equivFun.toLinearMap '' (L : Set V.V) := rfl
  rw [this, ← Submodule.map_span, span_eq_top_of_unimodular V L h hu, Submodule.map_top, LinearEquiv.range]

theorem herm_coord (V : Formalism.BasicNotions.HSpace E) (x y : V.V) :
    herm V.gramᵀ (V.frame.equivFun x) (V.frame.equivFun y) = V.hT y x := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change V.frame.repr x j * V.gram i j * star (V.frame.repr y i) = _
  ring

theorem selfDual_coordLat (V : Formalism.BasicNotions.HSpace E) (L : Submodule (𝓞 E) V.V)
    (h : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (x : Fin V.rank → E) :
    x ∈ coordLat V L ↔ ∀ y ∈ coordLat V L, IsIntegral ℤ (herm V.gramᵀ x y) := by
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
  have h1 : V.frame.equivFun x ∈ coordLat V L ↔ x ∈ L :=
    ⟨fun ⟨z, hz, e⟩ => V.frame.equivFun.injective e ▸ hz, fun hx => ⟨x, hx, rfl⟩⟩
  have h2 : x ∈ L ↔ ∀ y ∈ L, V.hT y x ∈ (1 : Submodule (𝓞 E) E) := by
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual V.hT L = L from h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  have h3 : ∀ z : E, z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := fun z =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  rw [h1, h2]
  constructor
  · rintro H _ ⟨y, hy, rfl⟩
    have := (h3 _).1 (H y hy)
    rwa [← herm_coord] at this
  · intro H y hy
    rw [h3, ← herm_coord]
    exact H _ ⟨y, hy, rfl⟩

theorem mem_latLoc_iff (V : Formalism.BasicNotions.HSpace E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (y : Fin V.rank → LocAlg v) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔ y ∈ locLattice v (coordLat V V.L0) := by
  have key : ∀ (a : v.adicCompletionIntegers (maximalRealSubfield E)) (b : v.adicCompletion (maximalRealSubfield E)) (z : E),
      a • (b ⊗ₜ[maximalRealSubfield E] z : LocAlg v) = ((a : v.adicCompletion (maximalRealSubfield E)) * b) ⊗ₜ z := by
    intro a b z
    rw [TensorProduct.smul_tmul']
    rfl
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have := Submodule.smul_mem (locLattice v (coordLat V V.L0)) (⟨a, ha⟩ : v.adicCompletionIntegers (maximalRealSubfield E))
        (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      convert this using 1
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hy
    suffices H : ∀ a : v.adicCompletionIntegers (maximalRealSubfield E),
        a • y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v by
      simpa using H 1
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy
      intro a
      refine AddSubgroup.subset_closure ⟨a, a.2, x, hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, locEmb_apply, key, mul_one]
      rfl
    | zero => intro a; rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
    | smul c x _ hx => intro a; rw [smul_smul]; exact hx _

theorem exists_conj (hc : CMData (maximalRealSubfield E) E) (V : Formalism.BasicNotions.HSpace E)
    (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) :
    ∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), HA (Fv (maximalRealSubfield E) v) hc.sig V.gram,
      {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
        (y : Fin V.rank → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
        y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔
          (HA.mat (Fv (maximalRealSubfield E) v) hc.sig V.gram (γ v)).1.mulVec y ∈
            GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v := by
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
    Formalism.L2.Pj.unramBridge_holds E fun P hP => by
      obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
        RingOfIntegers.ext e1.symm
      rwa [this]
  have hG : ∀ a b, cc (V.gramᵀ a b) = V.gramᵀ b a := fun a b => V.herm.eq (V.frame b) (V.frame a)
  have hd : V.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero
  obtain ⟨γ, hγ, hfin⟩ := (GlobalTheory.selfDual_lattices_one_genus hG hG hd hd (isLattice_coordLat V L h1 h2)
    (isLattice_coordLat V V.L0 V.standardTuple_isLattice V.baseLattice_isUnimodular)
    (Or.inl ⟨selfDual_coordLat V L h2, selfDual_coordLat V V.L0 V.baseLattice_isUnimodular⟩)).2.1 rfl
  have hmem : ∀ v, γ v ∈ HR (Fv (maximalRealSubfield E) v) hc.sig V.gram := fun v => by
    have h := congrArg Matrix.transpose (hγ v).1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h
    exact h.symm
  refine ⟨fun v => ⟨γ v, hmem v⟩, hfin.subset fun v hv h => hv (Subtype.ext h), fun v y => ?_⟩
  rw [mem_latLoc_iff]
  exact ((hγ v).2 y).trans (mem_latLoc_iff (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v _).symm

end

theorem exists_local_conjugation : ∀ (D : D7) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L), ∃ γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram, {v | γ v ≠ 1}.Finite ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) (GlobalTheory.VolRatioCompare.reLat V L h1 h2) v :=
  fun D V L h1 h2 =>
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    exists_conj (E := D.host.E) D.sp.cm V L h1 h2

end GlobalTheory.LocalConjugacy
