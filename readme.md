# lean-lam

Various experiments with lambda calculi and type systems in lean4. This is for learning purposes
only and does not contain useful or reusable code.

## Setup

- install nix
- (optional) do one of the following to get prebuilt lean4 binaries:
  - add the lean4 cachix (`nix-shell -p cachix --command "cachix use lean4"`)
  - add the lean4 cachix keys directly to your nix config (see [here](https://kha.github.io/lean4/doc/setup/nix.html))
- enter the shell (`nix develop`)
- install deps (`lake update`)
- update the mathlib cache (`lake exe cache get`)
