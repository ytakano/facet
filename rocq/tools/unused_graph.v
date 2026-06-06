Require dpdgraph.dpdgraph.

From Facet.TypeSystem Require
  CheckerSoundness
  CheckerUsageSoundness
  BorrowCheckSoundness
  EnvFullSoundness
  End2EndSafety
  TypeChecker.

Set DependGraph File "unused-analysis.dpd".

Print FileDependGraph
  Facet.TypeSystem.TypeChecker
  Facet.TypeSystem.CheckerSoundness
  Facet.TypeSystem.CheckerUsageSoundness
  Facet.TypeSystem.BorrowCheckSoundness
  Facet.TypeSystem.EnvFullSoundness
  Facet.TypeSystem.End2EndSafety.
