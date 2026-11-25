module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective

@[expose] public section

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Forms Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie
open NumberField IsDedekindDomain Matrix GlobalTheory.BigTop GlobalTheory.Mem.R3 GlobalTheory.Core.Rk.Top

section Conj

variable {ι : Type} [Fintype ι] {n : ℕ}

end Conj

variable {D : D7}

abbrev PtX (D : D7) : Type := Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

theorem reGL_symm_mem {F E : Type} [Field F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {a b : ℕ}
    (h : a = b) (J : Matrix (Fin a) (Fin a) E) {x} (hx : x ∈ Formalism.UG.UPts σ (J.reindex (finCongr h) (finCongr h)) R) :
    (reGL h _).symm x ∈ Formalism.UG.UPts σ J R := by
  subst h
  exact hx

theorem exists_hasMat (x : PtX D) : ∃ h, HasMat h x.1 := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram).surjective
    ⟨_, reGL_symm_mem _ _ (rankP D) _ x.2⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig D.sp.X'.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, fun i j => ?_⟩
  have e2 := (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram b).symm.trans (congrArg Subtype.val hb)
  exact congrArg (fun g : GL _ (Lev.EAf D) => g.1 i j) ((congrArg (Formalism.UG.bc (Lev.swapAE D)) k2).trans e2)

def rowPt (x : PtX D) : Bridge.Gf D.sp.X' := (finHom D.sp.X').rangeRestrict (exists_hasMat x).choose

def LevIs {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad)
    (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : S.U, HasMat h κ.1) ∧ ∀ h (κ : S.U), HasMat h κ.1 → χ h = star ((S.chi κ : ℂˣ) : ℂ)

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {R}

end Real

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

abbrev Coord : Type := p.R.cX.W →ₗ[ℂ] Pol ℂ D.what₂.Tau D.sp.X'.rank

variable (Cs : ColsTiedSym D) (tw : SymmetricTwistedColumnsAtPrimes p.Tp Cs ex.tw)




variable {p Cs tw} {co : Coord p} {e₀ e₀' : ∀ u, (D.mem u).P.Mt ≃ₗ[ℂ] D.what₂.Amb D.what₂.mu0}
  {e e' : ∀ u μ, (D.PTw u μ).Mt ≃ₗ[ℂ] D.what₂.Amb μ}

end Point

end GlobalTheory.EX

end
