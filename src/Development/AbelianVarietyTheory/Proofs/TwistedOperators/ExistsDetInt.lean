module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct

namespace GlobalTheory.VecInv

variable {D : D7}

def Stab (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) : Prop :=
  g ∈ GfC V ∧ finE V g ∈ St β

def UnrOff (b : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → b * (x : AE D) = b → χ x = 1


open Classical in
def adjDatum (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO S T) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
  else 0

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem Stab.one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Stab V β 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩

theorem Stab.inv {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (h : Stab V β g) : Stab V β g⁻¹ :=
  ⟨Subgroup.inv_mem _ h.1, by rw [map_inv]; exact Subgroup.inv_mem _ h.2⟩

theorem isFrame_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) : IsFrame (x * β) Λ := by
  first | exact _root_.GlobalTheory.StabLatInv.isFrame_mul_of_mem_St | exact @_root_.GlobalTheory.StabLatInv.isFrame_mul_of_mem_St | apply _root_.GlobalTheory.StabLatInv.isFrame_mul_of_mem_St <;> assumption

theorem mem_latO_iff {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)}
    {βT : GL (Fin T.rank) (Lev.EAf D)} (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) {g : GA D S} {h : GA D T}
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (u : WO S T) :
    u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u,
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
    fun g h hg hh u hu => GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS (isFrame_mul hS hg) hT
      (isFrame_mul hT hh) rfl rfl u hu
  refine ⟨key g h hg hh u, fun hu => ?_⟩
  have := key g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg) (by rw [map_inv]; exact inv_mem hh) _ hu
  have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at e
  rwa [e] at this

theorem exists_det_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β) :
    ∃ a : Formalism.L2.Herm.intAf D.host.F D.host.E, (a : Lev.EAf D) = toEAf D (Formalism.L2.Theta.mt V g).det ∧
      ∀ PP : Pl D.host.E, ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
        resS D.host.F PP a := by
  obtain ⟨y, hy⟩ := hg
  refine ⟨y.val.det, ?_, fun PP => ?_⟩
  · have h1 : toEAf D (Formalism.L2.Theta.mt V g).det = (finE V g).val.det := by
      rw [finE_val, RingHom.map_det]; rfl
    have h2 : (Matrix.GeneralLinearGroup.det (frGL β y)) = Matrix.GeneralLinearGroup.det (intGL _ _ _ y) := by
      simp [frGL]
    have h3 := congrArg Units.val h2
    rw [h1, ← hy]
    refine Eq.trans ?_ h3.symm
    exact (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.map_det y.val
  · rw [← hy, redFn_frGL]
    exact ((resS D.host.F PP).map_det y.val).symm

def detAt (e : AE D) (he : e * e = e) (V : HSp D) : GA D V →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => e * (Formalism.L2.Theta.mt V g).det + (1 - e)
      map_one' := by rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]; ring
      map_mul' := fun g g' => by
        rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.det_mul]
        linear_combination (-(Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g').det + (Formalism.L2.Theta.mt V g).det
          + (Formalism.L2.Theta.mt V g').det - 1) * he }

theorem isDetAt_detAt (e : AE D) (he : e * e = e) (V : HSp D) (g : GA D V) : IsDetAt e V g (detAt e he V g) := rfl

end GlobalTheory.VecInv

end
