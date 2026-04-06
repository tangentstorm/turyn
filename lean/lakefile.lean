import Lake
open Lake DSL

package turyn where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Turyn where
  roots := #[`Turyn]
