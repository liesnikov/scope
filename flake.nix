{
  description = "Agda scope library";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/eabe8d3eface69f5bb16c18f8662a702f50c20d5;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.mkAgdaDerivation.url = github:liesnikov/mkAgdaDerivation;
  inputs.agda2hs = {
    url = "github:liesnikov/agda2hs";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.mkAgdaDerivation.follows = "mkAgdaDerivation";
  };

  outputs = {self, nixpkgs, flake-utils, mkAgdaDerivation, agda2hs}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};
        agdaDerivation = pkgs.callPackage mkAgdaDerivation.lib.mkAgdaDerivation {};
        scope-lib = agdaDerivation
          { pname = "scope";
            meta = {};
            version = "0.1.0.0";
            tcDir = "src";
            buildInputs = [
              agda2hs.packages.${system}.agda2hs-lib
            ];
            src = ./.;
          };
      in {
        packages = {
          inherit scope-lib;
          default = scope-lib;
        };
      });
}