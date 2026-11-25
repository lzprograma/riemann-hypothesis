module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.NormBlowupInt

theorem isFinite_fromNormalization_int_of_isReduced {X Y : Scheme.{0}} {o : CommRingCat.{0}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsReduced X] [IsLocallyNoetherian X]
    (hess : ∀ x ∈ genericPoints X, (f.residueFieldMap x).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := genericPoints X
  have hD : Dense D := dense_iff_closure_eq.mpr genericPoints.closure
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := (GlobalTheory.finite_genericPoints_inter _ (f.isCompact_preimage hU.isCompact)).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType) (hess _ x.2.1)
  haveI (x : ι) := GlobalTheory.ZMain.finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)

theorem dense_preimage_of_blowup {Z X' : Scheme.{0}} (J : Z.IdealSheafData) (b : X' ⟶ Z)
    (hb : FinalTheorems.Blowup b J) (hiso : ∀ V : Z.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (b ∣_ V))
    (W : Z.Opens) (hWd : Dense (W : Set Z)) : Dense ((b ⁻¹ᵁ W : X'.Opens) : Set X') := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hD' : Dense (((J.comap b).support : Set X')ᶜ) := by
    rw [← hD, ← D.coe_nonzeroLocus_canonical]
    exact D.dense_nonzeroLocus_canonical
  let Uc : Z.Opens := J.support.compl
  haveI : IsIso (b ∣_ Uc) := hiso Uc fun x hx => hx
  haveI hoi : IsOpenImmersion ((b ⁻¹ᵁ Uc).ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  rw [dense_iff_inter_open]
  intro O hO hne
  obtain ⟨y, hyO, hy⟩ := hD'.inter_open_nonempty O hO hne
  have hyU : y ∈ b ⁻¹ᵁ Uc := by
    change b y ∉ J.support
    intro h
    exact hy ((GlobalTheory.ProjBlowup.mem_support_comap J b y).2 h)
  let O' : (b ⁻¹ᵁ Uc).toScheme.Opens := (b ⁻¹ᵁ Uc).ι ⁻¹ᵁ ⟨O, hO⟩
  have hopen : IsOpen (((b ⁻¹ᵁ Uc).ι ≫ b) '' (O' : Set (b ⁻¹ᵁ Uc).toScheme)) :=
    ((b ⁻¹ᵁ Uc).ι ≫ b).isOpenEmbedding.isOpenMap _ O'.isOpen
  obtain ⟨w, ⟨t, htO, rfl⟩, hwW⟩ := hWd.inter_open_nonempty _ hopen ⟨_, ⟨⟨y, hyU⟩, hyO, rfl⟩⟩
  refine ⟨(b ⁻¹ᵁ Uc).ι t, htO, ?_⟩
  change b ((b ⁻¹ᵁ Uc).ι t) ∈ W
  rwa [← Scheme.Hom.comp_apply]

end GlobalTheory.NormBlowupInt
