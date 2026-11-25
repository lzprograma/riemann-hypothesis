module

public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable

@[expose] public section

namespace GlobalTheory.HCXi

theorem xiExists_of_besselXiIntegrable : BesselXiIntegrable → Formalism.FourierDecayAlt.B.XiExists := fun h => h

end GlobalTheory.HCXi
