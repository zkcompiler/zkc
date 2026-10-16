module

public import ZkcExamples.Structured.MapFirstAssociations
public import ZkcExamples.Structured.MapPrefixAssociations

@[expose] public section
namespace ZkcExamples.Structured

/-! Separate complete source tables instantiate the same association constructors. -/

namespace MapFirstContractsInstance
open MapFirstViews

theorem first_bodies : MapFirstContracts.Bodies program.payload.definitions :=
  MapFirstAssociations.first_bodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem first_laws : MapFirstContracts.Laws (program.payload.meanings F G) :=
  MapFirstContracts.laws_of_bodies program.payload.linked first_bodies

end MapFirstContractsInstance

namespace MapPrefixContractsInstance
open MapPrefixViews

theorem first_bodies : MapFirstContracts.Bodies program.payload.definitions :=
  MapPrefixAssociations.first_bodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem first_laws : MapFirstContracts.Laws (program.payload.meanings F G) :=
  MapFirstContracts.laws_of_bodies program.payload.linked first_bodies

theorem prefix_bodies : MapPrefixContracts.Bodies program.payload.definitions :=
  MapPrefixAssociations.prefix_bodies

theorem prefix_laws : MapPrefixContracts.Laws (program.payload.meanings F G) :=
  MapPrefixContracts.laws_of_bodies program.payload.linked prefix_bodies first_bodies

end MapPrefixContractsInstance

end ZkcExamples.Structured
