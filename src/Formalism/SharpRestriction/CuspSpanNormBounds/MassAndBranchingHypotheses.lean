module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusMass

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

section Conclusion₂

variable (D : D7)

def Conclusion1 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ) : Prop :=
  UnitaryVolumeMass.stX D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c

def PointsLemma (u : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem3L0 D u

end Conclusion₂

section admitted

variable (D : D7)

def adm1 : Prop :=
  UnitaryVolumeMass.stMassRatio D

def adm2 : Prop :=
  UnitaryVolumeMass.stMassL D

def adm16 (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

def adm3 : Prop :=
  UnitaryVolumeMass.stBRmult

def ArchimedeanSignatureMatching : Prop :=
  UnitaryVolumeMass.stBRhad

def adm14 : Prop :=
  UnitaryVolumeMass.stBRtrans

def adm15 : Prop :=
  UnitaryVolumeMass.stBRmink

def adm5 : Prop :=
  UnitaryVolumeMass.stLem1 D

def adm6 : Prop :=
  UnitaryVolumeMass.HyperplaneRankAllWords D

def adm7 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def adm20 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def adm8 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def adm9 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

end admitted

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def adm10 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm11 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm12 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm17 (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def adm18 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm13 (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def adm19 (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

end Loc

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def admitted (C' Cl Cg cb Cu cT CT C0 A CSW δ Cn C1 Cq CPT CDl hilbertNinetyConstant CMo CK : ℝ) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 ∧ ArchimedeanSignatureMatching ∧ adm5 D ∧ adm6 D ∧
  adm7 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW ∧ adm8 D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧ adm9 D large₂ C' Cl Cg cb Cu cT CT C0 ∧
  adm10 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm11 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm12 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧
  adm13 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧ adm14 ∧ adm15 ∧ adm16 D G ∧
  adm17 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧ adm18 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧ adm19 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CK ∧
  adm20 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def Conclusion3Family : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, PointsLemma (Fm.D x i) u

end Family

end Formalism.MainNotions.VanishingOnXAndXPlusMass

end
