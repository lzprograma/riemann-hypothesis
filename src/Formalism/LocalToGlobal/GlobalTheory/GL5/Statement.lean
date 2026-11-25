module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions
open scoped TensorProduct

def FrameTied (D : D7) (Lv : LevelData D) : Prop :=
  letI := D.host.cmStar
  ∀ (u : D.what₂.Word) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (t : Fin D.R.k → v.adicCompletion D.host.F),
    (∃ y ∈ Formalism.L2.Herm.locL (F := D.host.F) (E := D.host.E) v (Lv u).Lb,
        ∀ a, ((Lv u).splitG i v h (y a)).1 = t a) ↔
      ∀ a, ((((Lv u).frG i v h)⁻¹ : GL (Fin D.R.k) (v.adicCompletion D.host.F)) :
        Matrix (Fin D.R.k) (Fin D.R.k) (v.adicCompletion D.host.F)).mulVec t a ∈
          v.adicCompletionIntegers D.host.F

def LandherrHasse (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ b : Fin W.rank → W.V, LinearIndependent D.host.E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0

def GenusMassStd (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D W.rank

def Link4p : Prop := ∀ (D : D7) (Lv : LevelData D), Formalism.MainNotions.StandardLattice.Conclusion4p D Lv

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
