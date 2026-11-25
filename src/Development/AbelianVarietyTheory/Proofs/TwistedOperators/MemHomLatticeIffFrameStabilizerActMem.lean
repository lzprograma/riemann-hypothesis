module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct




noncomputable section

namespace GlobalTheory.StabLatInv

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem intGL_mulVec_mem (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : ∀ i, x i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) :
    (intGL F E n y).val.mulVec x i ∈ Formalism.L2.Herm.intAf F E := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => mul_mem (y.val i j).2 (hx j)

theorem isFrame_mul_of_mem_St (β k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hk : k ∈ St β) : IsFrame (k * β) Λ := by
  obtain ⟨y, hy⟩ := hk
  have e : k * β = β * intGL F E n y := by
    rw [← hy]
    change β * intGL F E n y * β⁻¹ * β = _
    rw [inv_mul_cancel_right]
  intro x
  rw [hβ x, e, mul_inv_rev, ← map_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · exact intGL_mulVec_mem y⁻¹ _
  · intro h
    have h2 := intGL_mulVec_mem y _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h2

end General

theorem mem_latO_iff_actO_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u, u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  intro D S T ΛS ΛT βS βT _ _ hS hT g h hg hh u
  have hS' := isFrame_mul_of_mem_St βS _ ΛS hS hg
  have hT' := isFrame_mul_of_mem_St βT _ ΛT hT hh
  have eS : (finE S g * βS).val = (Formalism.L2.Theta.mt S g).map (toEAf D) * βS.val := rfl
  have eT : (finE T h * βT).val = (Formalism.L2.Theta.mt T h).map (toEAf D) * βT.val := rfl
  constructor
  · exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS hS' hT hT' eS eT u
  · intro hu
    have h1 := GlobalTheory.AdelicLatMove.actO_mem_latO S T g⁻¹ h⁻¹ ΛS ΛS ΛT ΛT _ βS _ βT hS' hS hT' hT
      (GlobalTheory.AdelicLatMove.frame_inv S g _ _ eS) (GlobalTheory.AdelicLatMove.frame_inv T h _ _ eT) _ hu
    have h2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
    rw [inv_inv, inv_inv] at h2
    rwa [h2] at h1

end GlobalTheory.StabLatInv

end
