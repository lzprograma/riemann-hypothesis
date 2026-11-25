module

public import Formalism.LocalToGlobal.UnitaryNorms.DatumS
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
namespace Host
end Host
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure HostDatumWithTies {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) where
  d3b : Host.PlacesOverCommonPrime D.host
  clsK : Host.ClsRepK D.host
  HE : Fld
  HE_fd : FiniteDimensional ℚ HE
def HostDatumSelfDual {ex : Extra D L hT Gi Gl K Y cX} (T : _root_.Formalism.L2.TiedDataSAlt ex) : Prop := Nonempty (_root_.Formalism.L2.HostDatumWithTies T)
end
end Formalism.L2
end
end
