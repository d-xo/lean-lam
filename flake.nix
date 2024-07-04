{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    lean4.url = "github:leanprover/lean4/v4.9.0";
  };

  outputs = ins : ins.flake-utils.lib.eachDefaultSystem (system : let
    pkgs = import ins.nixpkgs { inherit system; };
  in {
    devShells.default = pkgs.mkShell {
      buildInputs = [ ins.lean4.defaultPackage.${system} ];
    };
  });
}
