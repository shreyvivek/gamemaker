import Lake
open Lake DSL

package «test_project» where
  -- add package configuration options here

lean_lib «TestProject» where
  -- add library configuration options here

@[default_target]
lean_exe «test_project» where
  root := `Main
