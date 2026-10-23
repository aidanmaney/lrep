import Lake
open Lake DSL

package lrep where
  testDriver := "runner"

lean_lib Lrep where
  roots := #[`Lrep, `Lrep.Sound, `Lrep.Server, `Lrep.Diff, `Lrep.Dataflow, `Lrep.Runtime, `Lrep.Audit]

@[default_target]
lean_exe lrep where
  root := `Main

lean_exe runner where
  root := `tests.Runner
